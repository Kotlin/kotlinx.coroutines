/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.selects

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.TrySelectDetailedResult.*
import kotlin.contracts.*
import kotlin.coroutines.*
import kotlin.internal.*
import kotlin.jvm.*

/**
 * Waits for the result of multiple suspending functions simultaneously, which are specified using _clauses_
 * in the [builder] scope of this select invocation. The caller is suspended until one of the clauses
 * is either _selected_ or _fails_.
 *
 * At most one clause is *atomically* selected and its block is executed. The result of the selected clause
 * becomes the result of the select. If any clause _fails_, then the select invocation produces the
 * corresponding exception. No clause is selected in this case.
 *
 * This select function is _biased_ to the first clause. When multiple clauses can be selected at the same time,
 * the first one of them gets priority. Use [selectUnbiased] for an unbiased (randomized) selection among
 * the clauses.

 * There is no `default` clause for select expression. Instead, each selectable suspending function has the
 * corresponding non-suspending version that can be used with a regular `when` expression to select one
 * of the alternatives or to perform the default (`else`) action if none of them can be immediately selected.
 *
 * ### List of supported select methods
 *
 * | **Receiver**     | **Suspending function**                           | **Select clause**
 * | ---------------- | ---------------------------------------------     | -----------------------------------------------------
 * | [Job]            | [join][Job.join]                                  | [onJoin][Job.onJoin]
 * | [Deferred]       | [await][Deferred.await]                           | [onAwait][Deferred.onAwait]
 * | [SendChannel]    | [send][SendChannel.send]                          | [onSend][SendChannel.onSend]
 * | [ReceiveChannel] | [receive][ReceiveChannel.receive]                 | [onReceive][ReceiveChannel.onReceive]
 * | [ReceiveChannel] | [receiveCatching][ReceiveChannel.receiveCatching] | [onReceiveCatching][ReceiveChannel.onReceiveCatching]
 * | none             | [delay]                                           | [onTimeout][SelectBuilder.onTimeout]
 *
 * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this
 * function is suspended, this function immediately resumes with [CancellationException].
 * There is a **prompt cancellation guarantee**. If the job was cancelled while this function was
 * suspended, it will not resume successfully. See [suspendCancellableCoroutine] documentation for low-level details.
 *
 * Note that this function does not check for cancellation when it is not suspended.
 * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
 */
@OptIn(ExperimentalContracts::class)
public suspend inline fun <R> select(crossinline builder: SelectBuilder<R>.() -> Unit): R {
    contract {
        callsInPlace(builder, InvocationKind.EXACTLY_ONCE)
    }
    return SelectImplementation<R>(coroutineContext).run {
        builder(this)
        // TAIL-CALL OPTIMIZATION: the only
        // suspend call is at the last position.
        doSelect()
    }
}

/**
 * Scope for [select] invocation.
 *
 * An instance of [SelectBuilder] can only be retrieved as a receiver of a [select] block call,
 * and it is only valid during the registration phase of the select builder.
 * Any uses outside it lead to unspecified behaviour and are prohibited.
 *
 * The general rule of thumb is that instances of this type should always be used
 * implicitly and there shouldn't be any signatures mentioning this type,
 * whether explicitly (e.g. function signature) or implicitly (e.g. inferred `val` type).
 */
public sealed interface SelectBuilder<in R> {
    /**
     * Registers a clause in this [select] expression without additional parameters that does not select any value.
     */
    public operator fun SelectClause0.invoke(block: suspend () -> R)

    /**
     * Registers clause in this [select] expression without additional parameters that selects value of type [Q].
     */
    public operator fun <Q> SelectClause1<Q>.invoke(block: suspend (Q) -> R)

    /**
     * Registers clause in this [select] expression with additional parameter of type [P] that selects value of type [Q].
     */
    public operator fun <P, Q> SelectClause2<P, Q>.invoke(param: P, block: suspend (Q) -> R)

    /**
     * Registers clause in this [select] expression with additional nullable parameter of type [P]
     * with the `null` value for this parameter that selects value of type [Q].
     */
    public operator fun <P, Q> SelectClause2<P?, Q>.invoke(block: suspend (Q) -> R): Unit = invoke(null, block)

    /**
     * Clause that selects the given [block] after a specified timeout passes.
     * If timeout is negative or zero, [block] is selected immediately.
     *
     * **Note: This is an experimental api.** It may be replaced with light-weight timer/timeout channels in the future.
     *
     * @param timeMillis timeout time in milliseconds.
     */
    @ExperimentalCoroutinesApi
    @Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")
    @LowPriorityInOverloadResolution
    @Deprecated(
        message = "Replaced with the same extension function",
        level = DeprecationLevel.ERROR, replaceWith = ReplaceWith(expression = "onTimeout", imports = ["kotlinx.coroutines.selects.onTimeout"])
    )
    public fun onTimeout(timeMillis: Long, block: suspend () -> R): Unit = onTimeout(timeMillis, block)
}

/**
 * Each [select] clause is specified with:
 * 1) the [object of this clause][clauseObject],
 *    such as the channel instance for [SendChannel.onSend];
 * 2) the function that specifies how this clause
 *    should be registered in the object above;
 * 3) the function that modifies the internal result
 *    (passed via [SelectInstance.trySelect] or
 *    [SelectInstance.selectInRegistrationPhase])
 *    to the argument of the user-specified block.
 * 4) the function that specifies how the internal result provided via
 *    [SelectInstance.trySelect] or [SelectInstance.selectInRegistrationPhase]
 *    should be processed in case of this `select` cancellation while dispatching.
 */
@InternalCoroutinesApi
public sealed interface SelectClause {
    public val clauseObject: Any
    public val regFunc: RegistrationFunction
    public val processResFunc: ProcessResultFunction
    public val onCancellationConstructor: OnCancellationConstructor?
}

/**
 * The registration function specifies how the `select` instance should be registered into
 * the specified clause object. In case of channels, the registration logic
 * coincides with the plain `send/receive` operation with the only difference that
 * the `select` instance is stored as a waiter instead of continuation.
 */
@InternalCoroutinesApi
public typealias RegistrationFunction = (clauseObject: Any, select: SelectInstance<*>, param: Any?) -> Unit

/**
 * This function specifies how the _internal_ result, provided via [SelectInstance.selectInRegistrationPhase]
 * or [SelectInstance.trySelect] should be processed. For example, both [ReceiveChannel.onReceive] and
 * [ReceiveChannel.onReceiveCatching] clauses perform exactly the same synchronization logic,
 * but differ when the channel has been discovered in the closed or cancelled state.
 */
@InternalCoroutinesApi
public typealias ProcessResultFunction = (clauseObject: Any, param: Any?, clauseResult: Any?) -> Any?

/**
 * This function specifies how the internal result, provided via [SelectInstance.trySelect]
 * or [SelectInstance.selectInRegistrationPhase], should be processed in case of this `select`
 * cancellation while dispatching. Unfortunately, we cannot pass this function only in [SelectInstance.trySelect],
 * as [SelectInstance.selectInRegistrationPhase] can be called when the coroutine is already cancelled.
 */
@InternalCoroutinesApi
public typealias OnCancellationConstructor = (select: SelectInstance<*>, param: Any?, internalResult: Any?) -> (Throwable) -> Unit

/**
 * Clause for [select] expression without additional parameters that does not select any value.
 */
public sealed interface SelectClause0 : SelectClause

internal class SelectClause0Impl(
    override val clauseObject: Any,
    override val regFunc: RegistrationFunction,
    override val onCancellationConstructor: OnCancellationConstructor? = null
) : SelectClause0 {
    override val processResFunc: ProcessResultFunction = DUMMY_PROCESS_RESULT_FUNCTION
}
private val DUMMY_PROCESS_RESULT_FUNCTION: ProcessResultFunction = { _, _, _ -> null }

/**
 * Clause for [select] expression without additional parameters that selects value of type [Q].
 */
public sealed interface SelectClause1<out Q> : SelectClause

internal class SelectClause1Impl<Q>(
    override val clauseObject: Any,
    override val regFunc: RegistrationFunction,
    override val processResFunc: ProcessResultFunction,
    override val onCancellationConstructor: OnCancellationConstructor? = null
) : SelectClause1<Q>

/**
 * Clause for [select] expression with additional parameter of type [P] that selects value of type [Q].
 */
public sealed interface SelectClause2<in P, out Q> : SelectClause

internal class SelectClause2Impl<P, Q>(
    override val clauseObject: Any,
    override val regFunc: RegistrationFunction,
    override val processResFunc: ProcessResultFunction,
    override val onCancellationConstructor: OnCancellationConstructor? = null
) : SelectClause2<P, Q>

/**
 * Internal representation of `select` instance.
 *
 * @suppress **This is unstable API, and it is subject to change.**
 */
@InternalCoroutinesApi
public sealed interface SelectInstance<in R> {
    /**
     * The context of the coroutine that is performing this `select` operation.
     */
    public val context: CoroutineContext

    /**
     * This function should be called by other operations,
     * which are trying to perform a rendezvous with this `select`.
     * Returns `true` if the rendezvous succeeds, `false` otherwise.
     *
     * Note that according to the current implementation, a rendezvous attempt can fail
     * when either another clause is already selected or this `select` is still in
     * REGISTRATION phase. To distinguish the reasons, [SelectImplementation.trySelectDetailed]
     * function can be used instead.
     */
    public fun trySelect(clauseObject: Any, result: Any?): Boolean

    /**
     * When this `select` instance is stored as a waiter, the specified [handle][disposableHandle]
     * defines how the stored `select` should be removed in case of cancellation or another clause selection.
     */
    public fun disposeOnCompletion(disposableHandle: DisposableHandle)

    /**
     * When a clause becomes selected during registration, the corresponding internal result
     * (which is further passed to the clause's [ProcessResultFunction]) should be provided
     * via this function. After that, other clause registrations are ignored and [trySelect] fails.
     */
    public fun selectInRegistrationPhase(internalResult: Any?)
}
internal interface SelectInstanceInternal<R>: SelectInstance<R>, Waiter

@PublishedApi
internal open class SelectImplementation<R> constructor(
    override val context: CoroutineContext
) : CancelHandler(), SelectBuilder<R>, SelectInstanceInternal<R> {

    /**
     * Essentially, the `select` operation is split into three phases: REGISTRATION, WAITING, and COMPLETION.
     *
     * == Phase 1: REGISTRATION ==
     * In the first REGISTRATION phase, the user-specified [SelectBuilder] is applied, and all the listed clauses
     * are registered via the provided [registration functions][SelectClause.regFunc]. Intuitively, `select` clause
     * registration is similar to the plain blocking operation, with the only difference that this [SelectInstance]
     * is stored as a waiter instead of continuation, and [SelectInstance.trySelect] is used to make a rendezvous.
     * Also, when registering, it is possible for the operation to complete immediately, without waiting. In this case,
     * [SelectInstance.selectInRegistrationPhase] should be used. Otherwise, when no rendezvous happens and this `select`
     * instance is stored as a waiter, a completion handler for the registering clause should be specified via
     * [SelectInstance.disposeOnCompletion]; this handler specifies how to remove this `select` instance from the
     * clause object when another clause becomes selected or the operation cancels.
     *
     * After a clause registration is completed, another coroutine can attempt to make a rendezvous with this `select`.
     * However, to resolve a race between clauses registration and [SelectInstance.trySelect], the latter fails when
     * this `select` is still in REGISTRATION phase. Thus, the corresponding clause has to be registered again.
     *
     * In this phase, the `state` field stores either a special [STATE_REG] marker or
     * a list of clauses to be re-registered due to failed rendezvous attempts.
     *
     * == Phase 2: WAITING ==
     * If no rendezvous happens in REGISTRATION phase, the `select` operation moves to WAITING one and suspends until
     * [SelectInstance.trySelect] is called. Also, when waiting, this `select` can be cancelled. In the latter case,
     * further [SelectInstance.trySelect] attempts fail, and all the completion handlers, specified via
     * [SelectInstance.disposeOnCompletion], are invoked to remove this `select` instance from the corresponding
     * clause objects.
     *
     * In this phase, the `state` field stores either the continuation to be later resumed or a special `Cancelled`
     * object (with the cancellation cause inside) when this `select` becomes cancelled.
     *
     * == Phase 3: COMPLETION ==
     * Once a rendezvous happens either in REGISTRATION phase (via [SelectInstance.selectInRegistrationPhase]) or
     * in WAITING phase (via [SelectInstance.trySelect]), this `select` moves to the final `COMPLETION` phase.
     * First, the provided internal result is processed via the [ProcessResultFunction] of the selected clause;
     * it returns the argument for the user-specified block or throws an exception (see [SendChannel.onSend] as
     * an example). After that, this `select` should be removed from all other clause objects by calling the
     * corresponding [DisposableHandle]-s, provided via [SelectInstance.disposeOnCompletion] during registration.
     * At the end, the user-specified block is called and this `select` finishes.
     *
     * In this phase, once a rendezvous is happened, the `state` field stores the corresponding clause.
     * After that, it moves to [STATE_COMPLETED] to avoid memory leaks.
     *
     *
     *
     * The state machine is listed below:
     *
     *            REGISTRATION PHASE                   WAITING PHASE             COMPLETION PHASE
     *       ⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢             ⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢         ⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢
     *
     *                                                 +-----------+                 +-----------+
     *                                                 | CANCELLED |                 | COMPLETED |
     *                                                 +-----------+                 +-----------+
     *                                                       ^                             ^
     *     INITIAL STATE                                     |                             | this `select`
     *     ------------+                                     |  cancelled                  | is completed
     *                  \                                    |                             |
     *                   +=============+     move to     +------+    successful   +------------+
     *                +--|  STATE_REG  |---------------> | cont |-----------------| ClauseData |
     *                |  +=============+  WAITING phase  +------+  trySelect(..)  +------------+
     *                |    ^     |                                                       ^
     *                |    |     |    some clause has been selected during registration  |
     *         add a  |    |     +-------------------------------------------------------+
     *   clause to be |    |                                                             |
     *  re-registered |    | re-register                   some clause has been selected |
     *                |    | clauses                     during registration while there |
     *                v    |                            are clauses to be re-registered; |
     *          +------------------+                                   ignore the latter |
     *       +--| List<ClauseData> |-----------------------------------------------------+
     *       |  +------------------+
     *       |            ^
     *       |            |  add one more clause
     *       |            |  for re-registration
     *       +------------+
     *
     * One of the most valuable benefits of this `select` design is that it allows processing clauses
     * in a way similar to plain operations, such as `send` or `receive` on channels. The only difference
     * is that instead of continuation, the operation should store the provided `select` instance object.
     * Thus, this design makes it possible to support the `select` expression for any blocking data structure
     * in Kotlin Coroutines.
     *
     * It is worth mentioning that the algorithm above provides "obstruction-freedom" non-blocking guarantee
     * instead of the standard "lock-freedom" to avoid using heavy descriptors. In practice, this relaxation
     * does not make significant difference. However, it is vital for Kotlin Coroutines to provide some
     * non-blocking guarantee, as users may add blocking code in [SelectBuilder], and this blocking code
     * should not cause blocking behaviour in other places, such as an attempt to make a rendezvous with
     * the `select` that is hang in REGISTRATION phase.
     *
     * Also, this implementation is NOT linearizable under some circumstances. The reason is that a rendezvous
     * attempt with `select` (via [SelectInstance.trySelect]) may fail when this `select` operation is still
     * in REGISTRATION phase. Consider the following situation on two empty rendezvous channels `c1` and `c2`
     * and the `select` operation that tries to send an element to one of these channels. First, this `select`
     * instance is registered as a waiter in `c1`. After that, another thread can observe that `c1` is no longer
     * empty and try to receive an element from `c1` -- this receive attempt fails due to the `select` operation
     * being in REGISTRATION phase.
     * It is also possible to observe that this `select` operation registered in `c2` first, and only after that in
     * `c1` (it has to re-register in `c1` after the unsuccessful rendezvous attempt), which is also non-linearizable.
     * We, however, find such a non-linearizable behaviour not so important in practice and leverage the correctness
     * relaxation for the algorithm simplicity and the non-blocking progress guarantee.
     */

    /**
     * The state of this `select` operation. See the description above for details.
     */
    private val state = atomic<Any>(STATE_REG)
    /**
     * Returns `true` if this `select` instance is in the REGISTRATION phase;
     * otherwise, returns `false`.
     */
    private val inRegistrationPhase
        get() = state.value.let {
            it === STATE_REG || it is List<*>
        }
    /**
     * Returns `true` if this `select` is already selected;
     * thus, other parties are bound to fail when making a rendezvous with it.
     */
    private val isSelected
        get() = state.value is ClauseData<*>
    /**
     * Returns `true` if this `select` is cancelled.
     */
    private val isCancelled
        get() = state.value === STATE_CANCELLED

    /**
     * List of clauses waiting on this `select` instance.
     */
    private var clauses: MutableList<ClauseData<R>>? = ArrayList(2)

    /**
     * Stores the completion action provided through [disposeOnCompletion] or [invokeOnCancellation]
     * during clause registration. After that, if the clause is successfully registered
     * (so, it has not completed immediately), this handler is stored into
     * the corresponding [ClauseData] instance.
     *
     * Note that either [DisposableHandle] is provided, or a [Segment] instance with
     * the index in it, which specify the location of storing this `select`.
     * In the latter case, [Segment.onCancellation] should be called on completion/cancellation.
     */
    private var disposableHandleOrSegment: Any? = null

    /**
     * In case the disposable handle is specified via [Segment]
     * and index in it, implying calling [Segment.onCancellation],
     * the corresponding index is stored in this field.
     * The segment is stored in [disposableHandleOrSegment].
     */
    private var indexInSegment: Int = -1

    /**
     * Stores the result passed via [selectInRegistrationPhase] during clause registration
     * or [trySelect], which is called by another coroutine trying to make a rendezvous
     * with this `select` instance. Further, this result is processed via the
     * [ProcessResultFunction] of the selected clause.
     *
     * Unfortunately, we cannot store the result in the [state] field, as the latter stores
     * the clause object upon selection (see [ClauseData.clauseObject] and [SelectClause.clauseObject]).
     * Instead, it is possible to merge the [internalResult] and [disposableHandle] fields into
     * one that stores either result when the clause is successfully registered ([inRegistrationPhase] is `true`),
     * or [DisposableHandle] instance when the clause is completed during registration ([inRegistrationPhase] is `false`).
     * Yet, this optimization is omitted for code simplicity.
     */
    private var internalResult: Any? = NO_RESULT

    /**
     * This function is called after the [SelectBuilder] is applied. In case one of the clauses is already selected,
     * the algorithm applies the corresponding [ProcessResultFunction] and invokes the user-specified [block][ClauseData.block].
     * Otherwise, it moves this `select` to WAITING phase (re-registering clauses if needed), suspends until a rendezvous
     * is happened, and then completes the operation by applying the corresponding [ProcessResultFunction] and
     * invoking the user-specified [block][ClauseData.block].
     */
    @PublishedApi
    internal open suspend fun doSelect(): R =
        if (isSelected) complete()  // Fast path
        else doSelectSuspend()      // Slow path

    // We separate the following logic as it has two suspension points
    // and, therefore, breaks the tail-call optimization if it were
    // inlined in [doSelect]
    private suspend fun doSelectSuspend(): R {
        // In case no clause has been selected during registration,
        // the `select` operation suspends and waits for a rendezvous.
        waitUntilSelected() // <-- suspend call => no tail-call optimization here
        // There is a selected clause! Apply the corresponding
        // [ProcessResultFunction] and invoke the user-specified block.
        return complete() // <-- one more suspend call
    }

    // ========================
    // = CLAUSES REGISTRATION =
    // ========================

    override fun SelectClause0.invoke(block: suspend () -> R) =
        ClauseData<R>(clauseObject, regFunc, processResFunc, PARAM_CLAUSE_0, block, onCancellationConstructor).register()
    override fun <Q> SelectClause1<Q>.invoke(block: suspend (Q) -> R) =
        ClauseData<R>(clauseObject, regFunc, processResFunc, null, block, onCancellationConstructor).register()
    override fun <P, Q> SelectClause2<P, Q>.invoke(param: P, block: suspend (Q) -> R) =
        ClauseData<R>(clauseObject, regFunc, processResFunc, param, block, onCancellationConstructor).register()

    /**
     * Attempts to register this `select` clause. If another clause is already selected,
     * this function does nothing and completes immediately.
     * Otherwise, it registers this `select` instance in
     * the [clause object][ClauseData.clauseObject]
     * according to the provided [registration function][ClauseData.regFunc].
     * On success, this `select` instance is stored as a waiter
     * in the clause object -- the algorithm also stores
     * the provided via [disposeOnCompletion] completion action
     * and adds the clause to the list of registered one.
     * In case of registration failure, the internal result
     * (not processed by [ProcessResultFunction] yet) must be
     * provided via [selectInRegistrationPhase] -- the algorithm
     * updates the state to this clause reference.
     */
    @JvmName("register")
    internal fun ClauseData<R>.register(reregister: Boolean = false) {
        assert { state.value !== STATE_CANCELLED }
        // Is there already selected clause?
        if (state.value.let { it is ClauseData<*> }) return
        // For new clauses, check that there does not exist
        // another clause with the same object.
        if (!reregister) checkClauseObject(clauseObject)
        // Try to register in the corresponding object.
        if (tryRegisterAsWaiter(this@SelectImplementation)) {
            // Successfully registered, and this `select` instance
            // is stored as a waiter. Add this clause to the list
            // of registered clauses and store the provided via
            // [invokeOnCompletion] completion action into the clause.
            //
            // Importantly, the [waitUntilSelected] function is implemented
            // carefully to ensure that the cancellation handler has not been
            // installed when clauses re-register, so the logic below cannot
            // be invoked concurrently with the clean-up procedure.
            // This also guarantees that the list of clauses cannot be cleared
            // in the registration phase, so it is safe to read it with "!!".
            if (!reregister) clauses!! += this
            disposableHandleOrSegment = this@SelectImplementation.disposableHandleOrSegment
            indexInSegment = this@SelectImplementation.indexInSegment
            this@SelectImplementation.disposableHandleOrSegment = null
            this@SelectImplementation.indexInSegment = -1
        } else {
            // This clause has been selected!
            // Update the state correspondingly.
            state.value = this
        }
    }

    /**
     * Checks that there does not exist another clause with the same object.
     */
    private fun checkClauseObject(clauseObject: Any) {
        // Read the list of clauses, it is guaranteed that it is non-null.
        // In fact, it can become `null` only in the clean-up phase, while
        // this check can be called only in the registration one.
        val clauses = clauses!!
        // Check that there does not exist another clause with the same object.
        check(clauses.none { it.clauseObject === clauseObject }) {
            "Cannot use select clauses on the same object: $clauseObject"
        }
    }

    override fun disposeOnCompletion(disposableHandle: DisposableHandle) {
        this.disposableHandleOrSegment = disposableHandle
    }

    /**
     * An optimized version for the code below that does not allocate
     * a cancellation handler object and efficiently stores the specified
     * [segment] and [index].
     *
     * ```
     * disposeOnCompletion {
     *   segment.onCancellation(index, null)
     * }
     * ```
     */
    override fun invokeOnCancellation(segment: Segment<*>, index: Int) {
        this.disposableHandleOrSegment = segment
        this.indexInSegment = index
    }

    override fun selectInRegistrationPhase(internalResult: Any?) {
        this.internalResult = internalResult
    }

    // =========================
    // = WAITING FOR SELECTION =
    // =========================

    /**
     * Suspends and waits until some clause is selected. However, it is possible for a concurrent
     * coroutine to invoke [trySelect] while this `select` is still in REGISTRATION phase.
     * In this case, [trySelect] marks the corresponding select clause to be re-registered, and
     * this function performs registration of such clauses. After that, it atomically stores
     * the continuation into the [state] field if there is no more clause to be re-registered.
     */
    private suspend fun waitUntilSelected() = suspendCancellableCoroutine<Unit> sc@ { cont ->
        // Update the state.
        state.loop { curState ->
            when {
                // This `select` is in REGISTRATION phase, and there is no clause to be re-registered.
                // Perform a transition to WAITING phase by storing the current continuation.
                curState === STATE_REG -> if (state.compareAndSet(curState, cont)) {
                    // Perform a clean-up in case of cancellation.
                    //
                    // Importantly, we MUST install the cancellation handler
                    // only when the algorithm is bound to suspend. Otherwise,
                    // a race with [tryRegister] is possible, and the provided
                    // via [disposeOnCompletion] cancellation action can be ignored.
                    // Also, we MUST guarantee that this dispose handle is _visible_
                    // according to the memory model, and we CAN guarantee this when
                    // the state is updated.
                    cont.invokeOnCancellation(this.asHandler)
                    return@sc
                }
                // This `select` is in REGISTRATION phase, but there are clauses that has to be registered again.
                // Perform the required registrations and try again.
                curState is List<*> -> if (state.compareAndSet(curState, STATE_REG)) {
                    @Suppress("UNCHECKED_CAST")
                    curState as List<Any>
                    curState.forEach { reregisterClause(it) }
                }
                // This `select` operation became completed during clauses re-registration.
                curState is ClauseData<*> -> {
                    cont.resume(Unit, curState.createOnCancellationAction(this, internalResult))
                    return@sc
                }
                // This `select` cannot be in any other state.
                else -> error("unexpected state: $curState")
            }
        }
    }

    /**
     * Re-registers the clause with the specified
     * [clause object][clauseObject] after unsuccessful
     * [trySelect] of this clause while the `select`
     * was still in REGISTRATION phase.
     */
    private fun reregisterClause(clauseObject: Any) {
        val clause = findClause(clauseObject)!! // it is guaranteed that the corresponding clause is presented
        clause.disposableHandleOrSegment = null
        clause.indexInSegment = -1
        clause.register(reregister = true)
    }

    // ==============
    // = RENDEZVOUS =
    // ==============

    override fun trySelect(clauseObject: Any, result: Any?): Boolean =
        trySelectInternal(clauseObject, result) == TRY_SELECT_SUCCESSFUL

    /**
     * Similar to [trySelect] but provides a failure reason
     * if this rendezvous is unsuccessful. We need this function
     * in the channel implementation.
     */
    fun trySelectDetailed(clauseObject: Any, result: Any?) =
        TrySelectDetailedResult(trySelectInternal(clauseObject, result))

    private fun trySelectInternal(clauseObject: Any, internalResult: Any?): Int {
        while (true) {
            when (val curState = state.value) {
                // Perform a rendezvous with this select if it is in WAITING state.
                is CancellableContinuation<*> -> {
                    val clause = findClause(clauseObject) ?: continue // retry if `clauses` is already `null`
                    val onCancellation = clause.createOnCancellationAction(this@SelectImplementation, internalResult)
                    if (state.compareAndSet(curState, clause)) {
                        @Suppress("UNCHECKED_CAST")
                        val cont = curState as CancellableContinuation<Unit>
                        // Success! Store the resumption value and
                        // try to resume the continuation.
                        this.internalResult = internalResult
                        if (cont.tryResume(onCancellation)) return TRY_SELECT_SUCCESSFUL
                        // If the resumption failed, we need to clean
                        // the [result] field to avoid memory leaks.
                        this.internalResult = null
                        return TRY_SELECT_CANCELLED
                    }
                }
                // Already selected.
                STATE_COMPLETED, is ClauseData<*> -> return TRY_SELECT_ALREADY_SELECTED
                // Already cancelled.
                STATE_CANCELLED -> return TRY_SELECT_CANCELLED
                // This select is still in REGISTRATION phase, re-register the clause
                // in order not to wait until this select moves to WAITING phase.
                // This is a rare race, so we do not need to worry about performance here.
                STATE_REG -> if (state.compareAndSet(curState, listOf(clauseObject))) return TRY_SELECT_REREGISTER
                // This select is still in REGISTRATION phase, and the state stores a list of clauses
                // for re-registration, add the selecting clause to this list.
                // This is a rare race, so we do not need to worry about performance here.
                is List<*> -> if (state.compareAndSet(curState, curState + clauseObject)) return TRY_SELECT_REREGISTER
                // Another state? Something went really wrong.
                else -> error("Unexpected state: $curState")
            }
        }
    }

    /**
     * Finds the clause with the corresponding [clause object][SelectClause.clauseObject].
     * If the reference to the list of clauses is already cleared due to completion/cancellation,
     * this function returns `null`
     */
    private fun findClause(clauseObject: Any): ClauseData<R>? {
        // Read the list of clauses. If the `clauses` field is already `null`,
        // the clean-up phase has already completed, and this function returns `null`.
        val clauses = this.clauses ?: return null
        // Find the clause with the specified clause object.
        return clauses.find { it.clauseObject === clauseObject }
            ?: error("Clause with object $clauseObject is not found")
    }

    // ==============
    // = COMPLETION =
    // ==============

    /**
     * Completes this `select` operation after the internal result is provided
     * via [SelectInstance.trySelect] or [SelectInstance.selectInRegistrationPhase].
     * (1) First, this function applies the [ProcessResultFunction] of the selected clause
     * to the internal result.
     * (2) After that, the [clean-up procedure][cleanup]
     * is called to remove this `select` instance from other clause objects, and
     * make it possible to collect it by GC after this `select` finishes.
     * (3) Finally, the user-specified block is invoked
     * with the processed result as an argument.
     */
    private suspend fun complete(): R {
        assert { isSelected }
        // Get the selected clause.
        @Suppress("UNCHECKED_CAST")
        val selectedClause = state.value as ClauseData<R>
        // Perform the clean-up before the internal result processing and
        // the user-specified block invocation to guarantee the absence
        // of memory leaks. Collect the internal result before that.
        val internalResult = this.internalResult
        cleanup(selectedClause)
        // Process the internal result and invoke the user's block.
        return if (!RECOVER_STACK_TRACES) {
            // TAIL-CALL OPTIMIZATION: the `suspend` block
            // is invoked at the very end.
            val blockArgument = selectedClause.processResult(internalResult)
            selectedClause.invokeBlock(blockArgument)
        } else {
            // TAIL-CALL OPTIMIZATION: the `suspend`
            // function is invoked at the very end.
            // However, internally this `suspend` function
            // constructs a state machine to recover a
            // possible stack-trace.
            processResultAndInvokeBlockRecoveringException(selectedClause, internalResult)
        }
    }

    private suspend fun processResultAndInvokeBlockRecoveringException(clause: ClauseData<R>, internalResult: Any?): R =
        try {
            val blockArgument = clause.processResult(internalResult)
            clause.invokeBlock(blockArgument)
        } catch (e: Throwable) {
            // In the debug mode, we need to properly recover
            // the stack-trace of the exception; the tail-call
            // optimization cannot be applied here.
            recoverAndThrow(e)
        }

    /**
     * Invokes all [DisposableHandle]-s provided via
     * [SelectInstance.disposeOnCompletion] during
     * clause registrations.
     */
    private fun cleanup(selectedClause: ClauseData<R>) {
        assert { state.value == selectedClause }
        // Read the list of clauses. If the `clauses` field is already `null`,
        // a concurrent clean-up procedure has already completed, and it is safe to finish.
        val clauses = this.clauses ?: return
        // Invoke all cancellation handlers except for the
        // one related to the selected clause, if specified.
        clauses.forEach { clause ->
            if (clause !== selectedClause) clause.dispose()
        }
        // We do need to clean all the data to avoid memory leaks.
        this.state.value = STATE_COMPLETED
        this.internalResult = NO_RESULT
        this.clauses = null
    }

    // [CompletionHandler] implementation, must be invoked on cancellation.
    override fun invoke(cause: Throwable?) {
        // Update the state.
        state.update { cur ->
            // Finish immediately when this `select` is already completed.
            // Notably, this select might be logically completed
            // (the `state` field stores the selected `ClauseData`),
            // while the continuation is already cancelled.
            // We need to invoke the cancellation handler in this case.
            if (cur === STATE_COMPLETED) return
            STATE_CANCELLED
        }
        // Read the list of clauses. If the `clauses` field is already `null`,
        // a concurrent clean-up procedure has already completed, and it is safe to finish.
        val clauses = this.clauses ?: return
        // Remove this `select` instance from all the clause object (channels, mutexes, etc.).
        clauses.forEach { it.dispose() }
        // We do need to clean all the data to avoid memory leaks.
        this.internalResult = NO_RESULT
        this.clauses = null
    }

    /**
     * Each `select` clause is internally represented with a [ClauseData] instance.
      */
    internal class ClauseData<R>(
        @JvmField val clauseObject: Any, // the object of this `select` clause: Channel, Mutex, Job, ...
        private val regFunc: RegistrationFunction,
        private val processResFunc: ProcessResultFunction,
        private val param: Any?, // the user-specified param
        private val block: Any, // the user-specified block, which should be called if this clause becomes selected
        @JvmField val onCancellationConstructor: OnCancellationConstructor?
    ) {
        @JvmField var disposableHandleOrSegment: Any? = null
        @JvmField var indexInSegment: Int = -1

        /**
         * Tries to register the specified [select] instance in [clauseObject] and check
         * whether the registration succeeded or a rendezvous has happened during the registration.
         * This function returns `true` if this [select] is successfully registered and
         * is _waiting_ for a rendezvous, or `false` when this clause becomes
         * selected during registration.
         *
         * For example, the [Channel.onReceive] clause registration
         * on a non-empty channel retrieves the first element and completes
         * the corresponding [select] via [SelectInstance.selectInRegistrationPhase].
         */
        fun tryRegisterAsWaiter(select: SelectImplementation<R>): Boolean {
            assert { select.inRegistrationPhase || select.isCancelled }
            assert { select.internalResult === NO_RESULT }
            regFunc(clauseObject, select, param)
            return select.internalResult === NO_RESULT
        }

        /**
         * Processes the internal result provided via either
         * [SelectInstance.selectInRegistrationPhase] or
         * [SelectInstance.trySelect] and returns an argument
         * for the user-specified [block].
         *
         * Importantly, this function may throw an exception
         * (e.g., when the channel is closed in [Channel.onSend], the
         * corresponding [ProcessResultFunction] is bound to fail).
         */
        fun processResult(result: Any?) = processResFunc(clauseObject, param, result)

        /**
         * Invokes the user-specified block and returns
         * the final result of this `select` clause.
         */
        @Suppress("UNCHECKED_CAST")
        suspend fun invokeBlock(argument: Any?): R {
            val block = block
            // We distinguish no-argument and 1-argument
            // lambdas via special markers for the clause
            // parameters. Specifically, PARAM_CLAUSE_0
            // is always used with [SelectClause0], which
            // takes a no-argument lambda.
            //
            // TAIL-CALL OPTIMIZATION: we invoke
            // the `suspend` block at the very end.
            return if (this.param === PARAM_CLAUSE_0) {
                block as suspend () -> R
                block()
            } else {
                block as suspend (Any?) -> R
                block(argument)
            }
        }

        fun dispose() {
            with(disposableHandleOrSegment) {
                if (this is Segment<*>) {
                    this.onCancellation(indexInSegment, null)
                } else {
                    (this as? DisposableHandle)?.dispose()
                }
            }
        }

        fun createOnCancellationAction(select: SelectInstance<*>, internalResult: Any?) =
            onCancellationConstructor?.invoke(select, param, internalResult)
    }
}

private fun CancellableContinuation<Unit>.tryResume(onCancellation: ((cause: Throwable) -> Unit)?): Boolean {
    val token = tryResume(Unit, null, onCancellation) ?: return false
    completeResume(token)
    return true
}

// trySelectInternal(..) results.
private const val TRY_SELECT_SUCCESSFUL = 0
private const val TRY_SELECT_REREGISTER = 1
private const val TRY_SELECT_CANCELLED = 2
private const val TRY_SELECT_ALREADY_SELECTED = 3
// trySelectDetailed(..) results.
internal enum class TrySelectDetailedResult {
    SUCCESSFUL, REREGISTER, CANCELLED, ALREADY_SELECTED
}
private fun TrySelectDetailedResult(trySelectInternalResult: Int): TrySelectDetailedResult = when(trySelectInternalResult) {
    TRY_SELECT_SUCCESSFUL -> SUCCESSFUL
    TRY_SELECT_REREGISTER -> REREGISTER
    TRY_SELECT_CANCELLED -> CANCELLED
    TRY_SELECT_ALREADY_SELECTED -> ALREADY_SELECTED
    else -> error("Unexpected internal result: $trySelectInternalResult")
}

// Markers for REGISTRATION, COMPLETED, and CANCELLED states.
private val STATE_REG = Symbol("STATE_REG")
private val STATE_COMPLETED = Symbol("STATE_COMPLETED")
private val STATE_CANCELLED = Symbol("STATE_CANCELLED")
// As the selection result is nullable, we use this special
// marker for the absence of result.
private val NO_RESULT = Symbol("NO_RESULT")
// We use this marker parameter objects to distinguish
// SelectClause[0,1,2] and invoke the user-specified block correctly.
internal val PARAM_CLAUSE_0 = Symbol("PARAM_CLAUSE_0")
