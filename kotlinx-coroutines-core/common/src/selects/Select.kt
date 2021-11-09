/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:OptIn(ExperimentalContracts::class)

package kotlinx.coroutines.selects

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.intrinsics.*
import kotlinx.coroutines.sync.*
import kotlin.contracts.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import kotlin.jvm.*
import kotlin.native.concurrent.*
import kotlin.time.*

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
 * | [Mutex]          | [lock][Mutex.lock]                                | [onLock][Mutex.onLock]
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
public suspend inline fun <R> select(crossinline builder: SelectBuilder<R>.() -> Unit): R {
    contract {
        callsInPlace(builder, InvocationKind.EXACTLY_ONCE)
    }
    return SelectBuilderImpl<R>().run {
        prepare()
        builder(this)
        doSelect()
    }
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
 */
public suspend inline fun <R> selectUnbiased(crossinline builder: SelectBuilder<R>.() -> Unit): R {
    contract {
        callsInPlace(builder, InvocationKind.EXACTLY_ONCE)
    }
    return UnbiasedSelectBuilderImpl<R>().run {
        prepare()
        builder(this)
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
    public fun onTimeout(timeMillis: Long, block: suspend () -> R)
}

/**
 * Clause that selects the given [block] after the specified [timeout] passes.
 * If timeout is negative or zero, [block] is selected immediately.
 *
 * **Note: This is an experimental api.** It may be replaced with light-weight timer/timeout channels in the future.
 */
@ExperimentalCoroutinesApi
@ExperimentalTime
public fun <R> SelectBuilder<R>.onTimeout(timeout: Duration, block: suspend () -> R): Unit =
    onTimeout(timeout.toDelayMillis(), block)

@InternalCoroutinesApi
public sealed interface SelectClause {
    public val objForSelect: Any
    public val regFunc: RegistrationFunction
    public val processResFunc: ProcessResultFunction
}

/**
 * Clause for [select] expression without additional parameters that does not select any value.
 */
public interface SelectClause0 : SelectClause

@InternalCoroutinesApi
public class SelectClause0Impl(
    override val objForSelect: Any,
    override val regFunc: RegistrationFunction
) :  SelectClause0 {
    override val processResFunc: ProcessResultFunction = { objForSelect: Any, param: Any?, clauseResult: Any? -> clauseResult }
}

/**
 * Clause for [select] expression without additional parameters that selects value of type [Q].
 */
public interface SelectClause1<out Q> : SelectClause

@InternalCoroutinesApi
public class SelectClause1Impl<Q>(
    override val objForSelect: Any,
    override val regFunc: RegistrationFunction,
    override val processResFunc: ProcessResultFunction
) : SelectClause1<Q>

/**
 * Clause for [select] expression with additional parameter of type [P] that selects value of type [Q].
 */
public interface SelectClause2<in P, out Q> : SelectClause

@InternalCoroutinesApi
public class SelectClause2Impl<P, Q>(
    override val objForSelect: Any,
    override val regFunc: RegistrationFunction,
    override val processResFunc: ProcessResultFunction
) : SelectClause2<P, Q>
@InternalCoroutinesApi
public typealias RegistrationFunction = (objForSelect: Any, select: SelectInstance<*>, param: Any?) -> Unit
@InternalCoroutinesApi
public typealias ProcessResultFunction = (objForSelect: Any, param: Any?, clauseResult: Any?) -> Any?
@InternalCoroutinesApi
public typealias OnCompleteAction = () -> Unit

/**
 * Internal representation of select instance. This instance is called _selected_ when
 * the clause to execute is already picked.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
@InternalCoroutinesApi // todo: sealed interface https://youtrack.jetbrains.com/issue/KT-22286
public interface SelectInstance<in R> {
    /**
     * This function should be called by other operations which are trying to perform a rendezvous with this `select`.
     * If this another operation is [SelectInstance] then it should be passed as [from] parameter. Returns `true` if
     * the rendezvous succeeds, `false` otherwise.
     */
    public fun trySelect(objForSelect: Any, result: Any?): Boolean

    /**
     * This function should be called if this `select` is registered as a waiter. A function which removes the waiter
     * after this `select` is processed should be provided as a parameter.
     */
    public fun invokeOnCompletion(onCompleteAction: () -> Unit)

    /**
     * This function should be called during this `select` registration phase on a successful rendezvous.
     */
    public fun selectInRegPhase(selectResult: Any?)
}

@PublishedApi
internal class UnbiasedSelectBuilderImpl<R> : SelectBuilderImpl<R>() {
    private val clauses: MutableList<ClauseWithArguments> = arrayListOf()

    override fun SelectClause0.invoke(block: suspend () -> R) {
        clauses += ClauseWithArguments(this, null, block)
    }

    override fun <Q> SelectClause1<Q>.invoke(block: suspend (Q) -> R) {
        clauses += ClauseWithArguments(this, null, block)
    }

    override fun <P, Q> SelectClause2<P, Q>.invoke(param: P, block: suspend (Q) -> R) {
        clauses += ClauseWithArguments(this, param, block)
    }

    override suspend fun doSelect(): R {
        shuffleAndRegisterClauses()
        return super.doSelect()
    }

    private fun shuffleAndRegisterClauses() {
        clauses.shuffle()
        clauses.forEach {
            when (val clause = it.clause) {
                is SelectClause0 -> {
                    clause.register(it.block as suspend () -> R)
                }
                is SelectClause1<*> -> {
                    clause.register(it.block as suspend (Any?) -> R)
                }
                is SelectClause2<*, *> -> {
                    clause as SelectClause2<Any?, suspend (Any?) -> R>
                    clause.register(it.param, it.block as suspend (Any?) -> R)
                }
            }
        }
        clauses.clear()
    }
}

private class ClauseWithArguments(val clause: SelectClause, val param: Any?, val block: Any?)

@PublishedApi
internal open class SelectBuilderImpl<R> : SelectBuilder<R>, SelectInstance<R> {
    private val cont = atomic<Any?>(null)
    internal lateinit var context: CoroutineContext

    // 0: objForSelect
    // 1: RegistrationFunction
    // 2: ProcessResultFunction
    // 3: param
    // 4: block
    // 5: onCompleteAction
    private val alternatives = ArrayList<Any?>(ALTERNATIVE_SIZE * 2) // 2 clauses -- the most common case
    private var onCompleteAction: (() -> Unit)? = null

    private val state = atomic<Any>(STATE_REG)
    private val clauseResult = atomic<Any?>(RESULT_NULL)

    override fun invokeOnCompletion(onCompleteAction: () -> Unit) {
        this.onCompleteAction = onCompleteAction
    }

    override fun selectInRegPhase(selectResult: Any?) {
        this.clauseResult.value = selectResult
    }

    suspend fun prepare() {
        this.context = coroutineContext
    }

    open suspend fun doSelect(): R =
        selectAlternativeIteration(cleanOnCompletion = true)

    suspend fun selectAlternativeIteration(cleanOnCompletion: Boolean): R {
        if (trySelectAlternative()) {
            val block = this.block!!
            if (cleanOnCompletion) {
                cleanNonSelectedAlternatives(getObjForSelect())
                cleanBuilder()
            }
            return if (block is suspend () -> R) {
                block()
            } else {
                block as suspend (Any?) -> R
                block(clauseResult.value)
            }
        } else {
            return selectAlternativeIterationSuspend(cleanOnCompletion)
        }
    }

    private suspend fun selectAlternativeIterationSuspend(cleanOnCompletion: Boolean): R {
        selectAlternativeSuspend()
        val objForSelect = getObjForSelect()
        val i = selectedAlternativeIndex(objForSelect)
        val result = processResult(i)
        val param = alternatives[i + 3]
        val block = alternatives[i + 4]
        if (cleanOnCompletion) {
            cleanNonSelectedAlternatives(objForSelect)
            cleanBuilder()
        }
        return if (param === PARAM_CLAUSE_0) {
            block as suspend () -> R
            recoverStacktraceIfNeeded { block() }
        } else {
            block as suspend (Any?) -> R
            recoverStacktraceIfNeeded { block(result) }
        }
    }

    private inline fun <R> recoverStacktraceIfNeeded(block: () -> R): R = try {
        block()
    } catch (e: Throwable) {
        throw recoverStackTrace(e)
    }

    private fun cleanBuilder() {
        this.alternatives.clear()
        this.cont.value = null
        this.block = null
    }

    private fun processResult(i: Int): Any? {
        val objForSelect = alternatives[i]!!
        val processResFunc = alternatives[i + 2] as ProcessResultFunction
        val param = alternatives[i + 3]
        val clauseResult = this.clauseResult.value.also { this.clauseResult.lazySet(RESULT_NULL) }
        return processResFunc(objForSelect, param, clauseResult)
    }

    private fun addAlternative(
        objForSelect: Any,
        regFunc: RegistrationFunction,
        processResFunc: ProcessResultFunction,
        param: Any?,
        block: Any
    ): Boolean {
        if (clauseResult.value !== RESULT_NULL) return true
        checkObjForSelect(objForSelect)
        regFunc(objForSelect, this, param)
        if (clauseResult.value === RESULT_NULL) { // registered as waiter
            alternatives.add(objForSelect)
            alternatives.add(regFunc)
            alternatives.add(processResFunc)
            alternatives.add(param)
            alternatives.add(block)
            alternatives.add(onCompleteAction.also { onCompleteAction = null })
            return true
        } else { // rendezvous?
            storeObjForSelect(objForSelect)
            return false
        }
    }

    private fun checkObjForSelect(objForSelect: Any) {
        for (i in 0 until alternatives.size step ALTERNATIVE_SIZE) {
            check(alternatives[i] !== objForSelect) {
                "Cannot use matching select clauses on the same object"
            }
        }
    }

    private fun registerAlternative(i: Int): Boolean {
        val objForSelect = alternatives[i]!!
        val regFunc = alternatives[i + 1] as RegistrationFunction
        val param = alternatives[i + 3]
        regFunc(objForSelect, this, param)
        return if (clauseResult.value === RESULT_NULL) { // registered as waiter
            alternatives[i + 5] = onCompleteAction.also { onCompleteAction = null }
            true
        } else { // rendezvous?
            storeObjForSelect(objForSelect)
            false
        }
    }

    private fun trySelectAlternative(): Boolean {
        if (clauseResult.value !== RESULT_NULL) return true
        while (true) {
            val objForSelect = extractFromStackOrMarkWaiting() ?: break
            val i = selectedAlternativeIndex(objForSelect)
            if (!registerAlternative(i)) {
                this.clauseResult.value = processResult(i)
                this.block = alternatives[i + 4] as Function<R>
                return true
            }
        }
        return false
    }

    private suspend fun selectAlternativeSuspend() = suspendCancellableCoroutineReusable<Unit> { cont ->
        if (!this.cont.compareAndSet(null, cont)) cont.resume(Unit)
        cont.invokeOnCancellation { cleanNonSelectedAlternatives(null) }
    }

    /**
     * This function removes this `SelectInstance` from the
     * waiting queues of other alternatives.
     */
    fun cleanNonSelectedAlternatives(selectedObject: Any?) {
        val curState = state.getAndSet(STATE_DONE)
        clean@ for (i in 0 until alternatives.size / ALTERNATIVE_SIZE) {
            val i = i * ALTERNATIVE_SIZE
            val objForSelect = alternatives[i]
            if (selectedObject === objForSelect) continue
            var cur: Any = curState
            check@ while (true) {
                if (cur === objForSelect) continue@clean
                if (cur !is Node) break@check
                if (cur.objForSelect === objForSelect) continue@clean
                if (cur.next == null) break@check
                cur = cur.next!!
            }
            val onCompleteAction = alternatives[i + 5] as OnCompleteAction?
            onCompleteAction?.invoke()
        }
    }

    /**
     * Gets the act function and the block for the selected alternative and invoke it
     * with the specified result.
     */
    private suspend fun <R> invokeSelectedAlternativeAction(i: Int, result: Any?): R {
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
    private fun selectedAlternativeIndex(objForSelect: Any): Int {
        for (i in 0 until alternatives.size step ALTERNATIVE_SIZE) {
            if (alternatives[i] === objForSelect) return i
        }
        error("Object for select $objForSelect is not found")
    }

    override fun trySelect(objForSelect: Any, result: Any?): Boolean {
        if (!tryRendezvousOrReregister(objForSelect)) return false
        this.clauseResult.value = result
        if (this.cont.value === null && this.cont.compareAndSet(null, STATE_DONE)) return true
        this.cont.value!!.let { cont ->
            cont as CancellableContinuation<Unit>
            val resumeToken = cont.tryResume(Unit) ?: return false
            cont.completeResume(resumeToken)
            return true
        }
    }

    private fun tryRendezvousOrReregister(objForSelect: Any): Boolean = state.loop { curState ->
        when {
            curState === STATE_REG -> if (state.compareAndSet(curState, Node(objForSelect, null))) return false
            curState === STATE_WAITING -> if (state.compareAndSet(curState, objForSelect)) return true
            curState === STATE_DONE -> return false
            else -> if (state.compareAndSet(curState, Node(objForSelect, curState))) return false
        }
    }

    private fun extractFromStackOrMarkWaiting(): Any? = state.loop { curState ->
        when {
            curState === STATE_REG -> if (state.compareAndSet(curState, STATE_WAITING)) return null
            curState is Node -> {
                val updState = curState.next ?: STATE_REG
                if (state.compareAndSet(curState, updState)) return curState.objForSelect
            }
            else -> if (state.compareAndSet(curState, STATE_REG)) return curState
        }
    }

    private fun getObjForSelect(): Any {
        var cur: Any = state.value
        while (cur is Node) cur = cur.next!!
        return cur
    }

    private fun storeObjForSelect(objForSelect: Any): Unit = state.loop { curState ->
        when {
            curState === STATE_REG -> if (state.compareAndSet(STATE_REG, objForSelect)) return
            curState is Node -> {
                var lastNode: Node = curState
                while (lastNode.next != null) lastNode = lastNode.next as Node
                lastNode.next = objForSelect
                return
            }
            else -> if (state.compareAndSet(curState, Node(curState, objForSelect))) return
        }
    }

    private class Node(var objForSelect: Any?, var next: Any?)

    var block: Function<R>? = null

    override fun SelectClause0.invoke(block: suspend () -> R) =
        register(block)

    override fun <P, Q> SelectClause2<P, Q>.invoke(param: P, block: suspend (Q) -> R) =
        register(param, block)

    override fun <Q> SelectClause1<Q>.invoke(block: suspend (Q) -> R) =
        register(block)

    protected fun SelectClause0.register(block: suspend () -> R) {
        if (!addAlternative(objForSelect, regFunc, processResFunc, PARAM_CLAUSE_0, block)) {
            clauseResult.value = processResFunc(objForSelect, null, clauseResult.value)
            this@SelectBuilderImpl.block = block
        }
    }

    protected fun <Q> SelectClause1<Q>.register(block: suspend (Q) -> R) {
        if (!addAlternative(objForSelect, regFunc, processResFunc, PARAM_CLAUSE_1, block)) {
            clauseResult.value = processResFunc(objForSelect, null, clauseResult.value)
            this@SelectBuilderImpl.block = block
        }
    }

    protected fun <P, Q> SelectClause2<P, Q>.register(param: P, block: suspend (Q) -> R) {
        if (!addAlternative(objForSelect, regFunc, processResFunc, param, block)) {
            clauseResult.value = processResFunc(objForSelect, param, clauseResult.value)
            this@SelectBuilderImpl.block = block
        }
    }

    override fun onTimeout(timeMillis: Long, block: suspend () -> R) =
        OnTimeout(timeMillis).selectClause.invoke(block)
}

private class OnTimeout(
    private val timeMillis: Long
) {
    private fun register(select: SelectInstance<*>, ignoredParam: Any?) {
        if (timeMillis <= 0) {
            select.selectInRegPhase(Unit)
            return
        }
        val action = Runnable {
            select.trySelect(this@OnTimeout, Unit)
        }
        select as SelectBuilderImpl<*>
        val context = select.context
        val disposableHandle = context.delay.invokeOnTimeout(timeMillis, action, context)
        select.invokeOnCompletion { disposableHandle.dispose() }
    }

    val selectClause: SelectClause0 get() =
        SelectClause0Impl(
            objForSelect = this,
            regFunc = OnTimeout::register as RegistrationFunction
        )
}

// Number of items to be stored for each alternative in the `alternatives` array.
private const val ALTERNATIVE_SIZE = 6

private val STATE_REG = Symbol("REG")
private val STATE_WAITING = Symbol("WAITING")
private val STATE_DONE = Symbol("DONE")

private val RESULT_NULL = Symbol("NULL")

internal val PARAM_CLAUSE_0 = Symbol("PARAM_CLAUSE_0")
internal val PARAM_CLAUSE_1 = Symbol("PARAM_CLAUSE_1")