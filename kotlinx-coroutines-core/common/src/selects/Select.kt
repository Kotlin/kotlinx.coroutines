/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.selects

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.intrinsics.*
import kotlinx.coroutines.sync.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import kotlin.jvm.*

/**
 * Scope for [select] invocation.
 */
public interface SelectBuilder<in R> {
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
public interface SelectClause0 {
    /**
     * Registers this clause with the specified [select] instance and [block] of code.
     * @suppress **This is unstable API and it is subject to change.**
     */
    @InternalCoroutinesApi
    public fun <R> registerSelectClause0(select: SelectInstance<R>, block: suspend () -> R)
}

/**
 * Clause for [select] expression without additional parameters that selects value of type [Q].
 */
public interface SelectClause1<out Q> {
    /**
     * Registers this clause with the specified [select] instance and [block] of code.
     * @suppress **This is unstable API and it is subject to change.**
     */
    @InternalCoroutinesApi
    public fun <R> registerSelectClause1(select: SelectInstance<R>, block: suspend (Q) -> R)
}

/**
 * Clause for [select] expression with additional parameter of type [P] that selects value of type [Q].
 */
public interface SelectClause2<in P, out Q> {
    /**
     * Registers this clause with the specified [select] instance and [block] of code.
     * @suppress **This is unstable API and it is subject to change.**
     */
    @InternalCoroutinesApi
    public fun <R> registerSelectClause2(select: SelectInstance<R>, param: P, block: suspend (Q) -> R)
}

/**
 * Internal representation of select instance. This instance is called _selected_ when
 * the clause to execute is already picked.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
@InternalCoroutinesApi
public interface SelectInstance<in R> {
    /**
     * Returns `true` when this [select] statement had already picked a clause to execute.
     */
    public val isSelected: Boolean

    /**
     * Tries to select this instance.
     */
    public fun trySelect(idempotent: Any?): Boolean

    /**
     * Performs action atomically with [trySelect].
     */
    public fun performAtomicTrySelect(desc: AtomicDesc): Any?

    /**
     * Performs action atomically when [isSelected] is `false`.
     */
    public fun performAtomicIfNotSelected(desc: AtomicDesc): Any?

    /**
     * Returns completion continuation of this select instance.
     * This select instance must be _selected_ first.
     * All resumption through this instance happen _directly_ without going through dispatcher ([MODE_DIRECT]).
     */
    public val completion: Continuation<R>

    /**
     * Resumes this instance in a cancellable way ([MODE_CANCELLABLE]).
     */
    public fun resumeSelectCancellableWithException(exception: Throwable)

    /**
     * Disposes the specified handle when this instance is selected.
     */
    public fun disposeOnSelect(handle: DisposableHandle)
}

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
 * Note that this function does not check for cancellation when it is not suspended.
 * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
 */
public suspend inline fun <R> select(crossinline builder: SelectBuilder<R>.() -> Unit): R =
    suspendCoroutineUninterceptedOrReturn { uCont ->
        val scope = SelectBuilderImpl(uCont)
        try {
            builder(scope)
        } catch (e: Throwable) {
            scope.handleBuilderException(e)
        }
        scope.getResult()
    }


@SharedImmutable
internal val ALREADY_SELECTED: Any = Symbol("ALREADY_SELECTED")
@SharedImmutable
private val UNDECIDED: Any = Symbol("UNDECIDED")
@SharedImmutable
private val RESUMED: Any = Symbol("RESUMED")

@PublishedApi
internal class SelectBuilderImpl<in R>(
    private val uCont: Continuation<R> // unintercepted delegate continuation
) : LockFreeLinkedListHead(), SelectBuilder<R>,
    SelectInstance<R>, Continuation<R>, CoroutineStackFrame {
    override val callerFrame: CoroutineStackFrame?
        get() = uCont as? CoroutineStackFrame

    override fun getStackTraceElement(): StackTraceElement? = null

    // selection state is "this" (list of nodes) initially and is replaced by idempotent marker (or null) when selected
    private val _state = atomic<Any?>(this)

    // this is basically our own SafeContinuation
    private val _result = atomic<Any?>(UNDECIDED)

    // cancellability support
    @Volatile
    private var parentHandle: DisposableHandle? = null

    /* Result state machine

        +-----------+   getResult   +---------------------+   resume   +---------+
        | UNDECIDED | ------------> | COROUTINE_SUSPENDED | ---------> | RESUMED |
        +-----------+               +---------------------+            +---------+
              |
              | resume
              V
        +------------+  getResult
        | value/Fail | -----------+
        +------------+            |
              ^                   |
              |                   |
              +-------------------+
     */

    override val context: CoroutineContext get() = uCont.context

    override val completion: Continuation<R> get() = this

    private inline fun doResume(value: () -> Any?, block: () -> Unit) {
        check(isSelected) { "Must be selected first" }
        _result.loop { result ->
            when {
                result === UNDECIDED -> if (_result.compareAndSet(UNDECIDED, value())) return
                result === COROUTINE_SUSPENDED -> if (_result.compareAndSet(COROUTINE_SUSPENDED,
                        RESUMED
                    )) {
                    block()
                    return
                }
                else -> throw IllegalStateException("Already resumed")
            }
        }
    }

    // Resumes in MODE_DIRECT
    override fun resumeWith(result: Result<R>) {
        doResume({ result.toState() }) {
            if (result.isFailure) {
                uCont.resumeWithStackTrace(result.exceptionOrNull()!!)
            } else {
                uCont.resumeWith(result)
            }
        }
    }

    // Resumes in MODE_CANCELLABLE
    override fun resumeSelectCancellableWithException(exception: Throwable) {
        doResume({ CompletedExceptionally(exception) }) {
            uCont.intercepted().resumeCancellableWithException(exception)
        }
    }

    @PublishedApi
    internal fun getResult(): Any? {
        if (!isSelected) initCancellability()
        var result = _result.value // atomic read
        if (result === UNDECIDED) {
            if (_result.compareAndSet(UNDECIDED, COROUTINE_SUSPENDED)) return COROUTINE_SUSPENDED
            result = _result.value // reread volatile var
        }
        when {
            result === RESUMED -> throw IllegalStateException("Already resumed")
            result is CompletedExceptionally -> throw result.cause
            else -> return result // either COROUTINE_SUSPENDED or data
        }
    }

    private fun initCancellability() {
        val parent = context[Job] ?: return
        val newRegistration = parent.invokeOnCompletion(
            onCancelling = true, handler = SelectOnCancelling(parent).asHandler)
        parentHandle = newRegistration
        // now check our state _after_ registering
        if (isSelected) newRegistration.dispose()
    }

    private inner class SelectOnCancelling(job: Job) : JobCancellingNode<Job>(job) {
        // Note: may be invoked multiple times, but only the first trySelect succeeds anyway
        override fun invoke(cause: Throwable?) {
            if (trySelect(null))
                resumeSelectCancellableWithException(job.getCancellationException())
        }
        override fun toString(): String = "SelectOnCancelling[${this@SelectBuilderImpl}]"
    }

    private val state: Any? get() {
        _state.loop { state ->
            if (state !is OpDescriptor) return state
            state.perform(this)
        }
    }

    @PublishedApi
    internal fun handleBuilderException(e: Throwable) {
        if (trySelect(null)) {
            resumeWithException(e)
        } else {
            // Cannot handle this exception -- builder was already resumed with a different exception,
            // so treat it as "unhandled exception"
            handleCoroutineException(context, e)
        }
    }

    override val isSelected: Boolean get() = state !== this

    override fun disposeOnSelect(handle: DisposableHandle) {
        val node = DisposeNode(handle)
        while (true) { // lock-free loop on state
            val state = this.state
            if (state === this) {
                if (addLastIf(node, { this.state === this }))
                    return
            } else { // already selected
                handle.dispose()
                return
            }
        }
    }

    private fun doAfterSelect() {
        parentHandle?.dispose()
        forEach<DisposeNode> {
            it.handle.dispose()
        }
    }

    // it is just like start(), but support idempotent start
    override fun trySelect(idempotent: Any?): Boolean {
        check(idempotent !is OpDescriptor) { "cannot use OpDescriptor as idempotent marker"}
        while (true) { // lock-free loop on state
            val state = this.state
            when {
                state === this -> {
                    if (_state.compareAndSet(this, idempotent)) {
                        doAfterSelect()
                        return true
                    }
                }
                // otherwise -- already selected
                idempotent == null -> return false // already selected
                state === idempotent -> return true // was selected with this marker
                else -> return false
            }
        }
    }

    override fun performAtomicTrySelect(desc: AtomicDesc): Any? = AtomicSelectOp(desc, true).perform(null)
    override fun performAtomicIfNotSelected(desc: AtomicDesc): Any? = AtomicSelectOp(desc, false).perform(null)

    private inner class AtomicSelectOp(
        @JvmField val desc: AtomicDesc,
        @JvmField val select: Boolean
    ) : AtomicOp<Any?>() {
        override fun prepare(affected: Any?): Any? {
            // only originator of operation makes preparation move of installing descriptor into this selector's state
            // helpers should never do it, or risk ruining progress when they come late
            if (affected == null) {
                // we are originator (affected reference is not null if helping)
                prepareIfNotSelected()?.let { return it }
            }
            return desc.prepare(this)
        }

        override fun complete(affected: Any?, failure: Any?) {
            completeSelect(failure)
            desc.complete(this, failure)
        }

        fun prepareIfNotSelected(): Any? {
            _state.loop { state ->
                when {
                    state === this@AtomicSelectOp -> return null // already in progress
                    state is OpDescriptor -> state.perform(this@SelectBuilderImpl) // help
                    state === this@SelectBuilderImpl -> {
                        if (_state.compareAndSet(this@SelectBuilderImpl, this@AtomicSelectOp))
                            return null // success
                    }
                    else -> return ALREADY_SELECTED
                }
            }
        }

        private fun completeSelect(failure: Any?) {
            val selectSuccess = select && failure == null
            val update = if (selectSuccess) null else this@SelectBuilderImpl
            if (_state.compareAndSet(this@AtomicSelectOp, update)) {
                if (selectSuccess)
                    doAfterSelect()
            }
        }
    }

    override fun SelectClause0.invoke(block: suspend () -> R) {
        registerSelectClause0(this@SelectBuilderImpl, block)
    }

    override fun <Q> SelectClause1<Q>.invoke(block: suspend (Q) -> R) {
        registerSelectClause1(this@SelectBuilderImpl, block)
    }

    override fun <P, Q> SelectClause2<P, Q>.invoke(param: P, block: suspend (Q) -> R) {
        registerSelectClause2(this@SelectBuilderImpl, param, block)
    }

    override fun onTimeout(timeMillis: Long, block: suspend () -> R) {
        if (timeMillis <= 0L) {
            if (trySelect(null))
                block.startCoroutineUnintercepted(completion)
            return
        }
        val action = Runnable {
            // todo: we could have replaced startCoroutine with startCoroutineUndispatched
            // But we need a way to know that Delay.invokeOnTimeout had used the right thread
            if (trySelect(null))
                block.startCoroutineCancellable(completion) // shall be cancellable while waits for dispatch
        }
        disposeOnSelect(context.delay.invokeOnTimeout(timeMillis, action))
    }

    private class DisposeNode(
        @JvmField val handle: DisposableHandle
    ) : LockFreeLinkedListNode()
}
