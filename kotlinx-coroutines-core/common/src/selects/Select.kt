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
import kotlin.jvm.*
import kotlin.native.concurrent.*

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
 */
public interface SelectBuilder<in R> {
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
    @Deprecated(
        message = "Replaced with the same extension function",
        level = DeprecationLevel.HIDDEN, replaceWith = ReplaceWith("onTimeout")
    )
    public fun onTimeout(timeMillis: Long, block: suspend () -> R): Unit = onTimeout(timeMillis, block)
}

/**
 * Each [select] clause should be provided with:
 * 1) the [object of this clause][clauseObject],
 *    such as the channel instance for [Channel.onSend];
 * 2) the function that specifies how this clause
 *    should be registered in the object above;
 * 3) the function that modifies the resumption result
 *    (passed via [SelectInstance.trySelect]) to the argument
 *    of the user-specified block.
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
 * the specified clause object.
 */
@InternalCoroutinesApi
public typealias RegistrationFunction = (clauseObject: Any, select: SelectInstance<*>, param: Any?) -> Unit

/**
 *
 */
@InternalCoroutinesApi
public typealias ProcessResultFunction = (clauseObject: Any, param: Any?, clauseResult: Any?) -> Any?

/**
 *
 */
public typealias OnCancellationConstructor = (select: SelectInstance<*>, param: Any?, internalResult: Any?) -> (Throwable) -> Unit

/**
 * Clause for [select] expression without additional parameters that does not select any value.
 */
public interface SelectClause0 : SelectClause

@InternalCoroutinesApi
public class SelectClause0Impl(
    override val clauseObject: Any,
    override val regFunc: RegistrationFunction,
    override val onCancellationConstructor: OnCancellationConstructor? = null
) : SelectClause0 {
    override val processResFunc: ProcessResultFunction = DUMMY_PROCESS_RESULT_FUNCTION
}
@SharedImmutable
private val DUMMY_PROCESS_RESULT_FUNCTION: ProcessResultFunction = { _, _, _ -> null }

/**
 * Clause for [select] expression without additional parameters that selects value of type [Q].
 */
public interface SelectClause1<out Q> : SelectClause

@InternalCoroutinesApi
public class SelectClause1Impl<Q>(
    override val clauseObject: Any,
    override val regFunc: RegistrationFunction,
    override val processResFunc: ProcessResultFunction,
    override val onCancellationConstructor: OnCancellationConstructor? = null
) : SelectClause1<Q>

/**
 * Clause for [select] expression with additional parameter of type [P] that selects value of type [Q].
 */
public interface SelectClause2<in P, out Q> : SelectClause

@InternalCoroutinesApi
public class SelectClause2Impl<P, Q>(
    override val clauseObject: Any,
    override val regFunc: RegistrationFunction,
    override val processResFunc: ProcessResultFunction,
    override val onCancellationConstructor: OnCancellationConstructor? = null
) : SelectClause2<P, Q>

/**
 * Internal representation of select instance.
 *
 * @suppress **This is unstable API, and it is subject to change.**
 */
@InternalCoroutinesApi // todo: sealed interface https://youtrack.jetbrains.com/issue/KT-22286
public interface SelectInstance<in R> {
    /**
     * The context of the coroutine that is performing this `select` operation.
     */
    public val context: CoroutineContext

    /**
     * This function should be called by other operations,
     * which are trying to perform a rendezvous with this `select`.
     * Returns `true` if the rendezvous succeeds, `false` otherwise.
     */
    public fun trySelect(clauseObject: Any, result: Any?, onCancellation: ((Throwable) -> Unit)? = null): Boolean

    /**
     * Specifies how the stored as a waiter `select` instance should
     * be removed in case cancellation or another clause selection.
     */
    public fun disposeOnCompletion(disposableHandle: DisposableHandle)

    /**
     * When the registering clause becomes selected, the corresponding internal result
     * (which is further passed to the clause's [ProcessResultFunction]) should be provided
     * via this function. After that, other clause registrations are ignored.
     */
    public fun selectInRegistrationPhase(internalResult: Any?)
}

@PublishedApi
internal open class SelectImplementation<R> constructor(
    override val context: CoroutineContext
) : CancelHandler(), SelectBuilder<R>, SelectInstance<R> {

    /**
     * The `select` operation is split into three phases: REGISTRATION, WAITING, and COMPLETING.
     *
     * == Phase 1: Registration ==
     * In the first, registration phase, [SelectBuilder] is applied, and all the clauses register
     * via the provided [registration function][SelectClause.regFunc]. Intuitively, `select` registration
     * is similar to the plain blocking operation, with the only difference that this [SelectInstance]
     * is stored instead of continuation, and [SelectInstance.trySelect] is used to make a rendezvous.
     * Also, when registering, it is possible for the operation to complete immediately, without waiting.
     * In this case, [SelectInstance.selectInRegistrationPhase] should be used. Otherwise, when this
     * `select` instance is stored as a waiter, a completion handler should be specified via [SelectInstance.disposeOnCompletion].
     *
     * After the [SelectBuilder] is processed, the registration completes s
     *
     *
     * The state machine is listed below:
     *
     *            REGISTRATION PHASE                   WAITING PHASE             COMPLETING PHASE
     *       ⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢             ⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢         ⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢⌢
     *
     *                                                 +-----------+                 +-----------+
     *                                                 | Cancelled |                 | COMPLETED |
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
     */

    /**
     * The state of this `select` operation. See the description above for details.
     */
    private val state = atomic<Any>(STATE_REG)
    /**
     * Returns `true` if this `select` instance is in the registration phase;
     * otherwise, returns `false`.
     */
    private val inRegistrationPhase
        get() = state.value.let {
            it === STATE_REG || it is List<*>
        }
    /**
     * Returns `true` if this `select` is already selected or cancelled;
     * thus, other parties are bound to fail when making a rendezvous with it.
     */
    private val isSelected
        get() = state.value is ClauseData<*>

    private val isCancelled
        get() = state.value is Cancelled

    /**
     * List of clauses waiting on this `select` instance.
     */
    private var clauses: MutableList<ClauseData<R>> = ArrayList(2)

    /**
     * Stores the completion action provided through [disposeOnCompletion] during clause registration.
     * After that, if the clause is successfully registered (so, it has not completed immediately),
     * this [DisposableHandle] is stored into the corresponding [ClauseData] instance.
     */
    private var disposableHandle: DisposableHandle? = null

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
     * This function is called after [SelectBuilder] is applied. In case one of the clauses is already selected,
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
        ClauseData<R>(clauseObject, regFunc, processResFunc, PARAM_CLAUSE_1, block, onCancellationConstructor).register()
    override fun <P, Q> SelectClause2<P, Q>.invoke(param: P, block: suspend (Q) -> R) =
        ClauseData<R>(clauseObject, regFunc, processResFunc, param, block, onCancellationConstructor).register()

    /**
     * Attempts to register this `select` clause.
     * If another clause is already selected, this function
     * does nothing.
     * Otherwise, it registers this `select` instance in
     * the [clause object][ClauseData.clauseObject]
     * according to the [registration function][ClauseData.regFunc].
     * On success, this `select` instance is stored as a waiter
     * in the clause object -- the algorithm also stores
     * the provided via [disposeOnCompletion] completion action
     * and adds the clause to the list of registered one.
     * In case of registration failure, the internal result
     * (not processed by [ProcessResultFunction] yet) must be
     * provided via [selectInRegistrationPhase] -- the algorithm
     * updates the state to this clause reference.
     */
    protected fun ClauseData<R>.register(reregister: Boolean = false) {
        // Is there already selected clause?
        if (state.value.let { it is ClauseData<*> || it is Cancelled }) return
        // For new clauses, check that there does not exist
        // another clause with the same object.
        if (!reregister) checkClauseObject(clauseObject)
        // Try to register in the corresponding object.
        if (tryRegister(this@SelectImplementation)) {
            // Successfully registered, and this `select` instance
            // is stored as a waiter. Add this clause to the list
            // of registered clauses and store the provided via
            // [invokeOnCompletion] completion action into the clause.
            if (!reregister) clauses += this // TODO comment -- cancellation handler cannot be concurrent
            disposableHandle = this@SelectImplementation.disposableHandle // TODO bug is here
            this@SelectImplementation.disposableHandle = null
        } else {
            // This clause has been selected!
            // Update the state correspondingly.
            state.update {
                if (it is Cancelled) {
                    createOnCancellationAction(this@SelectImplementation, internalResult)?.invoke(it.cause)
                    return
                }
                this
            }
        }
    }

    /**
     * Checks that there does not exist another clause with the same object.
     */
    private fun checkClauseObject(clauseObject: Any) {
        check(!clauses.any { it.clauseObject === clauseObject }) {
            "Cannot use select clauses on the same object: $clauseObject"
        }
    }

    override fun disposeOnCompletion(disposableHandle: DisposableHandle) {
        this.disposableHandle = disposableHandle
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
    @OptIn(ExperimentalStdlibApi::class)
    private suspend fun waitUntilSelected() = suspendCancellableCoroutine<Unit> sc@ { cont ->
        // Update the state.
        state.loop { curState ->
            when {
                // This `select` is in REGISTRATION phase, and there is no clause to be re-registered.
                // Perform a transition to WAITING phase by storing the current continuation.
                curState === STATE_REG -> if (state.compareAndSet(curState, cont)) {
                    // Perform a clean-up in case of cancellation.
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
                // Cancelled
                curState is Cancelled -> return@sc
                // This `select` cannot be in any other state.
                else -> error("unexpected state: $curState")
            }
        }
    }

    private fun reregisterClause(clauseObject: Any) {
        val clause = findClause(clauseObject)
        clause.disposableHandle = null
        clause.register(reregister = true)
    }

    // ==============
    // = RENDEZVOUS =
    // ==============

    override fun trySelect(clauseObject: Any, result: Any?, onCancellation: ((Throwable) -> Unit)?): Boolean =
        trySelectInternal(clauseObject, result, onCancellation) == TRY_SELECT_SUCCESS

    public fun trySelectDetailed(clauseObject: Any, result: Any?, onCancellation: ((Throwable) -> Unit)? = null) =
        TrySelectDetailedResult(trySelectInternal(clauseObject, result, onCancellation))

    private fun trySelectInternal(clauseObject: Any, result: Any?, onCancellation: ((Throwable) -> Unit)?): Int {
        /**
         * Tries to select the specified clause and returns the suspended coroutine on success.
         * On failure, when another clause is already selected or this `select` operation is cancelled,
         * this function returns `null`.
         */
        while (true) {
            when (val curState = state.value) {
                // Perform a rendezvous with this select if it is in WAITING state.
                is CancellableContinuation<*> -> {
                    val clause = findClause(clauseObject) ?: continue
                    @Suppress("UNCHECKED_CAST")
                    if (state.compareAndSet(curState, clause)) {
                        val cont = curState as CancellableContinuation<Unit>
                        // Success! Store the resumption value and
                        // try to resume the continuation.
                        this.internalResult = result
                        if (cont.tryResume(onCancellation)) return TRY_SELECT_SUCCESS
                        // If the resumption failed, we need to clean
                        // the [result] field to avoid memory leaks.
                        this.internalResult = null
                        return TRY_SELECT_CANCELLED
                    }
                }
                // Already selected.
                STATE_COMPLETED, is ClauseData<*> -> return TRY_SELECT_ALREADY_SELECTED
                // Already cancelled.
                is Cancelled -> return TRY_SELECT_CANCELLED
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
     */
    private fun findClause(clauseObject: Any) =
        clauses.find { it.clauseObject === clauseObject } ?: error("Clause with object $clauseObject is not found")

    // ==============
    // = COMPLETING =
    // ==============

    /**
     * Completes this `select` operation. First, it applies the
     * [ProcessResultFunction] of the selected clause to the internal result,
     * which is provided via [SelectInstance.selectInRegistrationPhase] or
     * [SelectInstance.trySelect]. After that, the [clean-up procedure][cleanup]
     * is called to free all the referenced object for garbage collecting.
     * In the last, the user-specified blocked with the processed result
     * as an argument is invoked.
     */
    private suspend fun complete(): R {
        assert { isSelected }
        // Get the selected clause.
        @Suppress("UNCHECKED_CAST")
        val selectedClause = state.value as ClauseData<R>
        // Process the internal result.
        val blockArgument = selectedClause.processResult(internalResult)
        // Perform the clean-up before the user-specified block
        // invocation to guarantee the absence of memory leaks.
        cleanup(selectedClause)
        // TAIL-CALL OPTIMIZATION: the `suspend` block
        // is invoked at the very end.
        return selectedClause.invokeBlock(blockArgument)
    }

    /**
     * Invokes all [DisposableHandle]-s provided via
     * [SelectInstance.disposeOnCompletion] during clauses
     * registration, and clears all the references to avoid
     * memory leaks.
     */
    private fun cleanup(selectedClause: ClauseData<R>? = null) {
        assert { state.value == selectedClause }
        state.value = STATE_COMPLETED
        // Invoke all cancellation handlers except for the
        // one related to the selected clause, if specified.
        clauses.forEach { clause ->
            if (clause !== selectedClause) clause.disposableHandle?.dispose()
        }
    }

    // [CompletionHandler] implementation, must be invoked on cancellation.
    override fun invoke(cause: Throwable?) {
        val update = Cancelled(cause ?: CancellationException("This select has been cancelled"))
        state.update { cur ->
            if (cur is ClauseData<*> || cur == STATE_COMPLETED) return
            update
        }
        clauses.forEach { it.disposableHandle?.dispose() }
    }

    /**
     * Each `select` clause is internally represented with a [ClauseData] instance.
      */
    protected class ClauseData<R>(
        @JvmField val clauseObject: Any, // the object of this `select` clause: Channel, Mutex, Job, ...
        private val regFunc: RegistrationFunction,
        private val processResFunc: ProcessResultFunction,
        private val param: Any?,
        private val block: Any,
        @JvmField val onCancellationConstructor: OnCancellationConstructor?,
        @JvmField var disposableHandle: DisposableHandle? = null
    ) {
        /**
         * Try to register the specified `select` instance in [clauseObject].
         * Returns `true` if the `select` is successfully registered and
         * is waiting for a rendezvous, or `false` when this clause becomes
         * selected during registration (e.g., a [Channel.onReceive] registration
         * on a non-empty channel retrieves the first element and completes
         * the corresponding `select` operation).
         */
        fun tryRegister(select: SelectImplementation<R>): Boolean {
            assert { select.inRegistrationPhase || select.isCancelled }
            assert { select.internalResult === NO_RESULT }
            regFunc(clauseObject, select, param)
            return select.internalResult === NO_RESULT
        }

        /**
         * Processes the internal result, which is provided
         * via either [SelectInstance.selectInRegistrationPhase]
         * or [SelectInstance.trySelect], and returns an argument
         * for the user-specified [block].
         *
         * Importantly, this function is eligible to throw an exception
         * (e.g., when the channel is closed in [Channel.onSend], the
         * corresponding [ProcessResultFunction] is bound to fail).
         */
        fun processResult(result: Any?) = try {
            processResFunc(clauseObject, param, result)
        } catch (e: Throwable) {
            throw recoverStackTrace(e)
        }

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

        fun createOnCancellationAction(select: SelectInstance<*>, internalResult: Any?) =
            onCancellationConstructor?.invoke(select, param, internalResult)
    }
}

private fun CancellableContinuation<Unit>.tryResume(onCancellation: ((cause: Throwable) -> Unit)?): Boolean {
    val token = tryResume(Unit, null, onCancellation) ?: return false
    completeResume(token)
    return true
}

// Cancelled state with the specified cause.
private class Cancelled(@JvmField val cause: Throwable)

// trySelectInternal(..) results.
private const val TRY_SELECT_SUCCESS = 0
private const val TRY_SELECT_REREGISTER = 1
private const val TRY_SELECT_CANCELLED = 2
private const val TRY_SELECT_ALREADY_SELECTED = 3
// trySelectDetailed(..) results.
internal enum class TrySelectDetailedResult {
    SUCCESSFUL, REREGISTERING, CANCELLED, ALREADY_SELECTED
}
private fun TrySelectDetailedResult(internalResult: Int): TrySelectDetailedResult = when(internalResult) {
    TRY_SELECT_SUCCESS -> SUCCESSFUL
    TRY_SELECT_REREGISTER -> REREGISTERING
    TRY_SELECT_CANCELLED -> CANCELLED
    TRY_SELECT_ALREADY_SELECTED -> ALREADY_SELECTED
    else -> error("Unexpected internal result: $internalResult")
}

// Markers for REGISTRATION and COMPLETED states.
@SharedImmutable
private val STATE_REG = Symbol("STATE_REG")
@SharedImmutable
private val STATE_COMPLETED = Symbol("STATE_COMPLETED")
// As the selection result is nullable, we use this special
// marker for the absence of result.
@SharedImmutable
private val NO_RESULT = Symbol("NO_RESULT")
// We use this marker parameter objects to distinguish
// SelectClause[0,1,2] and invoke the `block` correctly.
@SharedImmutable
internal val PARAM_CLAUSE_0 = Symbol("PARAM_CLAUSE_0")
@SharedImmutable
internal val PARAM_CLAUSE_1 = Symbol("PARAM_CLAUSE_1")