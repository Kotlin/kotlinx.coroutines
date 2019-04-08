/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.selects

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.intrinsics.startCoroutineUnintercepted
import kotlinx.coroutines.sync.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import kotlin.math.*
import kotlin.random.Random

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
 * of the alternatives or to perform default (`else`) action if none of them can be immediately selected.
 *
 * | **Receiver**     | **Suspending function**                       | **Select clause**                                | **Non-suspending version**
 * | ---------------- | --------------------------------------------- | ------------------------------------------------ | --------------------------
 * | [Job]            | [join][Job.join]                              | [onJoin][Job.onJoin]                             | [isCompleted][Job.isCompleted]
 * | [Deferred]       | [await][Deferred.await]                       | [onAwait][Deferred.onAwait]                      | [isCompleted][Job.isCompleted]
 * | [SendChannel]    | [send][SendChannel.send]                      | [onSend][SendChannel.onSend]                     | [offer][SendChannel.offer]
 * | [ReceiveChannel] | [receive][ReceiveChannel.receive]             | [onReceive][ReceiveChannel.onReceive]            | [poll][ReceiveChannel.poll]
 * | [ReceiveChannel] | [receiveOrNull][ReceiveChannel.receiveOrNull] | [onReceiveOrNull][ReceiveChannel.onReceiveOrNull]| [poll][ReceiveChannel.poll]
 * | [Mutex]          | [lock][Mutex.lock]                            | [onLock][Mutex.onLock]                           | [tryLock][Mutex.tryLock]
 * | none             | [delay]                                       | [onTimeout][SelectBuilder.onTimeout]             | none
 *
 * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this
 * function is suspended, this function immediately resumes with [CancellationException].
 *
 * Atomicity of cancellation depends on the clause: [onSend][SendChannel.onSend], [onReceive][ReceiveChannel.onReceive],
 * [onReceiveOrNull][ReceiveChannel.onReceiveOrNull], and [onLock][Mutex.onLock] clauses are
 * *atomically cancellable*. When select throws [CancellationException] it means that those clauses had not performed
 * their respective operations.
 * As a side-effect of atomic cancellation, a thread-bound coroutine (to some UI thread, for example) may
 * continue to execute even after it was cancelled from the same thread in the case when this select operation
 * was already resumed on atomically cancellable clause and the continuation was posted for execution to the thread's queue.
 *
 * Note, that this function does not check for cancellation when it is not suspended.
 * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
 */
public suspend inline fun <R> select(crossinline builder: SelectBuilder<R>.() -> Unit): R =
    SelectBuilderImpl<R>().run {
        builder(this)
        doSelect()
    }

/**
 * Waits for the result of multiple suspending functions simultaneously like [select], but in an _unbiased_
 * way when multiple clauses are selectable at the same time.
 *
 * This unbiased implementation of `select` expression randomly shuffles the clauses before checking
 * if they are selectable, thus ensuring that there is no statistical bias to the selection of the first
 * clauses.
 *
 * See [select] function description for all the other details.
 *
 * @suppress Use [select] with [SelectBuilder.unbiased] option instead.
 */
@Deprecated(level = DeprecationLevel.WARNING, message = "Use `select` with `SelectBuilder.unbiased` option instead.")
public suspend inline fun <R> selectUnbiased(crossinline builder: SelectBuilder<R>.() -> Unit): R =
    SelectBuilderImpl<R>().run {
        builder(this)
        unbiased = true
        doSelect()
    }


/**
 * Scope for [select] invocation.
 */
public interface SelectBuilder<in R> {
    /**
     * If set to `true` this `select` expression randomly shuffles the clauses before checking if they are selectable,
     * thus ensuring that there is no statistical bias to the selection of the first clauses.
     */
    public var unbiased: Boolean

    /**
     * Registers clause in this [select] expression without additional parameters that does not select any value.
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
     * Registers clause in this [select] expression with additional parameter nullable parameter of type [P]
     * with the `null` value for this parameter that selects value of type [Q].
     */
    public operator fun <P, Q> SelectClause2<P?, Q>.invoke(block: suspend (Q) -> R) = invoke(null, block)

    /**
     * Clause that selects the given [block] after a specified timeout passes.
     * If timeout is negative or zero, [block] is selected immediately.
     *
     * **Note: This is an experimental api.** It may be replaced with light-weight timer/timeout channels in the future.
     *
     * @param timeMillis timeout time in milliseconds.
     */
    @ExperimentalCoroutinesApi
    public fun onTimeout(timeMillis: Long, block: suspend () -> R)
}

/**
 * Clause for [select] expression without additional parameters that does not select any value.
 */
public interface SelectClause0 : SelectClause
internal class SelectClause0Impl(
        override val objForSelect: Any,
        override val regFunc: RegistrationFunction,
        override val processResFunc: ProcessResultFunction
) : SelectClause0

/**
 * Clause for [select] expression without additional parameters that selects value of type [Q].
 */
public interface SelectClause1<out Q> : SelectClause
internal class SelectClause1Impl<Q>(
        override val objForSelect: Any,
        override val regFunc: RegistrationFunction,
        override val processResFunc: ProcessResultFunction
) : SelectClause1<Q>

/**
 * Clause for [select] expression with additional parameter of type [P] that selects value of type [Q].
 */
public interface SelectClause2<in P, out Q> : SelectClause
internal class SelectClause2Impl<P, Q>(
        override val objForSelect: Any,
        override val regFunc: RegistrationFunction,
        override val processResFunc: ProcessResultFunction
) : SelectClause2<P, Q>

@InternalCoroutinesApi
public interface SelectClause {
    val objForSelect: Any
    val regFunc: RegistrationFunction
    val processResFunc: ProcessResultFunction
}

public typealias RegistrationFunction = (objForSelect: Any, select: SelectInstance<*>, param: Any?) -> Unit
public typealias ProcessResultFunction = (objForSelect: Any, selectResult: Any?) -> Any?
public typealias OnCompleteAction = () -> Unit

/**
 * Internal representation of select instance. This instance is called _selected_ when
 * the clause to execute is already picked.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
@InternalCoroutinesApi
public interface SelectInstance<in R> {
    /**
     * An unique integer id
     */
    val id: Long

    /**
     * If this `select` operation is trying to make a rendezvous with another `select` operation which is in the
     * `WAITING` phase, it should store this another `select` operation into this field. It is required to be able
     * to find and resolve deadlocks.
     */
    var waitingFor: SelectInstance<*>?

    /**
     * This function should be called by other operations which are trying to perform a rendezvous with this `select`.
     * If this another operation is [SelectInstance] then it should be passed as [from] parameter. Returns `true` if
     * the rendezvous succeeds, `false` otherwise.
     */
    fun trySelect(objForSelect: Any, result: Any?, from: SelectInstance<*>? = null): Boolean

    /**
     * This function should be called if this `select` is registered as a waiter. A function which removes the waiter
     * after this `select` is processed should be provided as a parameter.
     */
    fun invokeOnCompletion(onCompleteAction: () -> Unit)

    /**
     * This function should be called during this `select` registration phase on a successful rendezvous.
     */
    fun selectInRegPhase(selectResult: Any?)
}

@SharedImmutable
internal val ALREADY_SELECTED: Any = Symbol("ALREADY_SELECTED")
@SharedImmutable
private val UNDECIDED: Any = Symbol("UNDECIDED")
@SharedImmutable
private val RESUMED: Any = Symbol("RESUMED")

@PublishedApi
internal class SelectBuilderImpl<R> : SelectBuilder<R>, SelectInstance<R> {
    lateinit var cont: CancellableContinuation<Any?>
    override val id = ID_GENERATOR.getAndIncrement()
    override var waitingFor: SelectInstance<*>? = null
    override var unbiased: Boolean = false

    // TODO bridge with old SelectBuilderImpl (getResult + handleException + constructor) + test

    // 0: objForSelect
    // 1: RegistrationFunction
    // 2: ProcessResultFunction
    // 3: param
    // 4: block
    // 5: onCompleteAction
    private val alternatives = ArrayList<Any?>(ALTERNATIVE_SIZE * 2) // 2 clauses -- the most common case

    private var resultOrOnCompleteAction: Any? = null
    private val state = atomic<Any?>(STATE_REG)

    override fun invokeOnCompletion(onCompleteAction: () -> Unit) {
        resultOrOnCompleteAction = onCompleteAction
    }

    override fun selectInRegPhase(selectResult: Any?) {
        state.value = STATE_DONE
        resultOrOnCompleteAction = selectResult
    }

    suspend fun doSelect(): R {
        if (unbiased) shuffleAlternatives()
        val resumeResult = try {
            selectAlternative()
        } catch (e: Throwable) {
            cleanState()
            cleanNonSelectedAlternatives(-1)
            throw e
        }
        val i = selectedAlternativeIndex()
        cleanNonSelectedAlternatives(i)
        cleanState()
        val result = processResult(i, resumeResult)
        return invokeSelectedAlternativeAction(i, result)
    }

    private fun cleanState() {
        state.value = STATE_DONE
    }

    private fun processResult(i: Int, resumeResule: Any?): Any? {
        val objForSelect = alternatives[i]!!
        val processResFunc = alternatives[i + 2] as ProcessResultFunction
        return processResFunc(objForSelect, resumeResule)
    }

    internal fun addAlternative(objForSelect: Any, regFunc: RegistrationFunction, processResFunc: ProcessResultFunction, param: Any?, block: Any) {
        alternatives.add(objForSelect)
        alternatives.add(regFunc)
        alternatives.add(processResFunc)
        alternatives.add(param)
        alternatives.add(block)
        alternatives.add(null)
    }

    /**
     * Shuffles alternatives for the _unbiased_ mode.
     */
    private fun shuffleAlternatives() {
        // TODO implement me
        // Random.nextInt()
    }

    suspend fun selectAlternative(): Any? {
        for (i in 0 until alternatives.size step ALTERNATIVE_SIZE) {
            val objForSelect = alternatives[i]!!
            val regFunc = alternatives[i + 1] as RegistrationFunction
            val param = alternatives[i + 3]
            regFunc(objForSelect, this, param)
            if (state.value === STATE_REG) {
                // successfully registered
                alternatives[i + 5] = resultOrOnCompleteAction.also { resultOrOnCompleteAction = null }
            } else {
                state.value = objForSelect
                // rendezvous happened
                return resultOrOnCompleteAction.also { resultOrOnCompleteAction = null }
            }
        }
        return suspendAtomicCancellableCoroutine { cont ->
            this.cont = cont
            this.state.value = STATE_WAITING
        }
    }

    /**
     * This function removes this `SelectInstance` from the
     * waiting queues of other alternatives.
     */
    fun cleanNonSelectedAlternatives(selectedIndex: Int) {
        for (i in 0 until alternatives.size step ALTERNATIVE_SIZE) {
            if (i / ALTERNATIVE_SIZE == selectedIndex) continue
            val onCompleteAction = (alternatives[i + 5] as OnCompleteAction?)
            if (onCompleteAction === null) break // can be null in case this alternative has not been processed
            onCompleteAction()
        }
    }
    /**
     * Gets the act function and the block for the selected alternative and invoke it
     * with the specified result.
     */
    suspend fun <R> invokeSelectedAlternativeAction(i: Int, result: Any?): R {
        val param = alternatives[i + 3]
        val block = alternatives[i + 4]
        return if (param === PARAM_CLAUSE_0) {
            block as suspend () -> R
            block()
        } else {
            block as suspend (Any?) -> R
            block(result)
        }
    }

    /**
     * Return an index of the selected alternative in `alternatives` array.
     */
    private fun selectedAlternativeIndex(): Int {
        val objForSelect = state.value!!
        for (i in 0 until alternatives.size step ALTERNATIVE_SIZE) {
            if (alternatives[i] === objForSelect) return i
        }
        error("Object for select $objForSelect is not found")
    }

    override fun trySelect(objForSelect: Any, result: Any?, from: SelectInstance<*>?): Boolean {
        from?.waitingFor = this
        try {
            var curState: Any? = this.state.value
            while (curState === STATE_REG) {
                // TODO backoff + Thread.onSpinWait
                // TODO AbstractQueuedSynchronizer?
                if (from != null && shouldBreakDeadlock(from, from, from.id)) return false
                curState = this.state.value
            }
            if (curState != STATE_WAITING) return false
            if (!state.compareAndSet(STATE_WAITING, objForSelect)) return false
            val resumeToken = cont.tryResume(result) ?: return false
            cont.completeResume(resumeToken)
            return true
        } finally {
            from?.waitingFor = null
        }
    }

    private fun shouldBreakDeadlock(start: SelectInstance<*>, cur: SelectInstance<*>, curMin: Long): Boolean {
        val next = cur.waitingFor ?: return false
        val newMin = min(curMin, next.id)
        if (next === start) return newMin == start.id
        return shouldBreakDeadlock(start, next, newMin)
    }

    override fun SelectClause0.invoke(block: suspend () -> R) =
        addAlternative(objForSelect, regFunc, processResFunc, PARAM_CLAUSE_0, block)

    override fun <Q> SelectClause1<Q>.invoke(block: suspend (Q) -> R) =
        addAlternative(objForSelect, regFunc, processResFunc, PARAM_CLAUSE_1, block)

    override fun <P, Q> SelectClause2<P, Q>.invoke(param: P, block: suspend (Q) -> R) =
        addAlternative(objForSelect, regFunc, processResFunc, param, block)

    override fun onTimeout(timeMillis: Long, block: suspend () -> R) = TODO("Not supported yet")
}

private val ID_GENERATOR = atomic(0L)
// Number of items to be stored for each alternative in the `alternatives` array.
private const val ALTERNATIVE_SIZE = 6

private val STATE_REG = Symbol("STATE_REG")
private val STATE_WAITING = Symbol("STATE_WAITING")
private val STATE_DONE = Symbol("STATE_DONE")

internal val PARAM_CLAUSE_0 = Symbol("PARAM_CLAUSE_0")
private val PARAM_CLAUSE_1 = Symbol("PARAM_CLAUSE_1")