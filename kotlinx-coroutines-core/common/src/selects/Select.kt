/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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
@InternalCoroutinesApi // todo: sealed interface https://youtrack.jetbrains.com/issue/KT-22286
public interface SelectInstance<in R> {
    /**
     * Returns `true` when this [select] statement had already picked a clause to execute.
     */
    public val isSelected: Boolean

    /**
     * Tries to select this instance. Returns `true` on success.
     */
    public fun trySelect(): Boolean

    /**
     * Tries to select this instance. Returns:
     * * [RESUME_TOKEN] on success,
     * * [RETRY_ATOMIC] on deadlock (needs retry, it is only possible when [otherOp] is not `null`)
     * * `null` on failure to select (already selected).
     * [otherOp] is not null when trying to rendezvous with this select from inside of another select.
     * In this case, [PrepareOp.finishPrepare] must be called before deciding on any value other than [RETRY_ATOMIC].
     *
     * Note, that this method's actual return type is `Symbol?` but we cannot declare it as such, because this
     * member is public, but [Symbol] is internal. When [SelectInstance] becomes a `sealed interface`
     * (see KT-222860) we can declare this method as internal.
     */
    public fun trySelectOther(otherOp: PrepareOp?): Any?

    /**
     * Performs action atomically with [trySelect].
     * May return [RETRY_ATOMIC], caller shall retry with **fresh instance of desc**.
     */
    public fun performAtomicTrySelect(desc: AtomicDesc): Any?

    /**
     * Returns completion continuation of this select instance.
     * This select instance must be _selected_ first.
     * All resumption through this instance happen _directly_ without going through dispatcher.
     */
    public val completion: Continuation<R>

    /**
     * Resumes this instance in a dispatched way with exception.
     * This method can be called from any context.
     */
    public fun resumeSelectWithException(exception: Throwable)

    /**
     * Disposes the specified handle when this instance is selected.
     * Note, that [DisposableHandle.dispose] could be called multiple times.
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
 * of the alternatives or to perform the default (`else`) action if none of them can be immediately selected.
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
    return suspendCoroutineUninterceptedOrReturn { uCont ->
        val scope = SelectBuilderImpl(uCont)
        try {
            builder(scope)
        } catch (e: Throwable) {
            scope.handleBuilderException(e)
        }
        scope.getResult()
    }
}


@SharedImmutable
internal val NOT_SELECTED: Any = Symbol("NOT_SELECTED")
@SharedImmutable
internal val ALREADY_SELECTED: Any = Symbol("ALREADY_SELECTED")
@SharedImmutable
private val UNDECIDED: Any = Symbol("UNDECIDED")
@SharedImmutable
private val RESUMED: Any = Symbol("RESUMED")

// Global counter of all atomic select operations for their deadlock resolution
// The separate internal class is work-around for Atomicfu's current implementation that creates public classes
// for static atomics
internal class SeqNumber {
    private val number = atomic(1L)
    fun next() = number.incrementAndGet()
}

@SharedImmutable
private val selectOpSequenceNumber = SeqNumber()

@PublishedApi
internal class SelectBuilderImpl<in R>(
    private val uCont: Continuation<R> // unintercepted delegate continuation
) : LockFreeLinkedListHead(), SelectBuilder<R>,
    SelectInstance<R>, Continuation<R>, CoroutineStackFrame
{
    override val callerFrame: CoroutineStackFrame?
        get() = uCont as? CoroutineStackFrame

    override fun getStackTraceElement(): StackTraceElement? = null

    // selection state is NOT_SELECTED initially and is replaced by idempotent marker (or null) when selected
    private val _state = atomic<Any?>(NOT_SELECTED)

    // this is basically our own SafeContinuation
    private val _result = atomic<Any?>(UNDECIDED)

    // cancellability support
    private val _parentHandle = atomic<DisposableHandle?>(null)
    private var parentHandle: DisposableHandle?
        get() = _parentHandle.value
        set(value) { _parentHandle.value = value }

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
        assert { isSelected } // "Must be selected first"
        _result.loop { result ->
            when {
                result === UNDECIDED -> {
                    val update = value()
                    if (_result.compareAndSet(UNDECIDED, update)) return
                }
                result === COROUTINE_SUSPENDED -> if (_result.compareAndSet(COROUTINE_SUSPENDED, RESUMED)) {
                    block()
                    return
                }
                else -> throw IllegalStateException("Already resumed")
            }
        }
    }

    // Resumes in direct mode, without going through dispatcher. Should be called in the same context.
    override fun resumeWith(result: Result<R>) {
        doResume({ result.toState() }) {
            if (result.isFailure) {
                uCont.resumeWithStackTrace(result.exceptionOrNull()!!)
            } else {
                uCont.resumeWith(result)
            }
        }
    }

    // Resumes in dispatched way so that it can be called from an arbitrary context
    override fun resumeSelectWithException(exception: Throwable) {
        doResume({ CompletedExceptionally(recoverStackTrace(exception, uCont)) }) {
            uCont.intercepted().resumeWith(Result.failure(exception))
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
            if (trySelect())
                resumeSelectWithException(job.getCancellationException())
        }
    }

    @PublishedApi
    internal fun handleBuilderException(e: Throwable) {
        if (trySelect()) {
            resumeWithException(e)
        } else if (e !is CancellationException) {
            /*
             * Cannot handle this exception -- builder was already resumed with a different exception,
             * so treat it as "unhandled exception". But only if  it is not the completion reason
             *  and it's not the cancellation. Otherwise, in the face of structured concurrency
             * the same exception will be reported to the global exception handler.
             */
            val result = getResult()
            if (result !is CompletedExceptionally || unwrap(result.cause) !== unwrap(e)) {
                handleCoroutineException(context, e)
            }
        }
    }

    override val isSelected: Boolean get() = _state.loop { state ->
        when {
            state === NOT_SELECTED -> return false
            state is OpDescriptor -> state.perform(this) // help
            else -> return true // already selected
        }
    }

    override fun disposeOnSelect(handle: DisposableHandle) {
        val node = DisposeNode(handle)
        // check-add-check pattern is Ok here since handle.dispose() is safe to be called multiple times
        if (!isSelected) {
            addLast(node) // add handle to list
            // double-check node after adding
            if (!isSelected) return // all ok - still not selected
        }
        // already selected
        handle.dispose()
    }

    private fun doAfterSelect() {
        parentHandle?.dispose()
        forEach<DisposeNode> {
            it.handle.dispose()
        }
    }

    override fun trySelect(): Boolean {
        val result = trySelectOther(null)
        return when {
            result === RESUME_TOKEN -> true
            result == null -> false
            else -> error("Unexpected trySelectIdempotent result $result")
        }
    }

    /*
       Diagram for rendezvous between two select operations:

       +---------+         +------------------------+ state(c)
       | Channel |         |  SelectBuilderImpl(1)  | -----------------------------------+
       +---------+         +------------------------+                                    |
            | queue                   ^                                                  |
            V                         | select                                           |
       +---------+  next   +------------------------+  next   +--------------+           |
       | LLHead  | ------> |  Send/ReceiveSelect(3) | -+----> | NextNode ... |           |
       +---------+         +------------------------+  |      +--------------+           |
            ^                              ^           | next(b)     ^                   |
            |                     affected |           V             |                   |
            |                          +-----------------+  next     |                   V
            |                          | PrepareOp(6)    | ----------+           +-----------------+
            |                          +-----------------+ <-------------------- | PairSelectOp(7) |
            |                                 | desc                             +-----------------+
            |                                 V
            |                  queue   +----------------------+
            +------------------------- | TryPoll/OfferDesc(5) |
                                       +----------------------+
                                     atomicOp |    ^
                                              V    | desc
       +----------------------+  impl  +---------------------+
       | SelectBuilderImpl(2) | <----- |  AtomicSelectOp(4)  |
       +----------------------+        +---------------------+
                    | state(a)                   ^
                    |                            |
                    +----------------------------+


       0. The first select operation SelectBuilderImpl(1) had already registered Send/ReceiveSelect(3) node
          in the channel.
       1. The second select operation SelectBuilderImpl(2) is trying to rendezvous calling
          performAtomicTrySelect(TryPoll/TryOfferDesc).
       2. A linked pair of AtomicSelectOp(4) and TryPoll/OfferDesc(5) is created to initiate this operation.
       3. AtomicSelectOp.prepareSelectOp installs a reference to AtomicSelectOp(4) in SelectBuilderImpl(2).state(a)
          field. STARTING AT THIS MOMENT CONCURRENT HELPERS CAN DISCOVER AND TRY TO HELP PERFORM THIS OPERATION.
       4. Then TryPoll/OfferDesc.prepare discovers "affectedNode" for this operation as Send/ReceiveSelect(3) and
          creates PrepareOp(6) that references it. It installs reference to PrepareOp(6) in Send/ReceiveSelect(3).next(b)
          instead of its original next pointer that was stored in PrepareOp(6).next.
       5. PrepareOp(6).perform calls TryPoll/OfferDesc(5).onPrepare which validates that PrepareOp(6).affected node
          is of the correct type and tries to secure ability to resume it by calling affected.tryResumeSend/Receive.
          Note, that different PrepareOp instances can be repeatedly created for different candidate nodes. If node is
          found to be be resumed/selected, then REMOVE_PREPARED result causes Send/ReceiveSelect(3).next change to
          undone and new PrepareOp is created with a different candidate node. Different concurrent helpers may end up
          creating different PrepareOp instances, so it is important that they ultimately come to consensus about
          node on which perform operation upon.
       6. Send/ReceiveSelect(3).affected.tryResumeSend/Receive forwards this call to SelectBuilderImpl.trySelectOther,
          passing it a reference to PrepareOp(6) as an indication of the other select instance rendezvous.
       7. SelectBuilderImpl.trySelectOther creates PairSelectOp(7) and installs it as SelectBuilderImpl(1).state(c)
          to secure the state of the first builder and commit ability to make it selected for this operation.
       8. NOW THE RENDEZVOUS IS FULLY PREPARED via descriptors installed at
          - SelectBuilderImpl(2).state(a)
          - Send/ReceiveSelect(3).next(b)
          - SelectBuilderImpl(1).state(c)
          Any concurrent operation that is trying to access any of the select instances or the queue is going to help.
          Any helper that helps AtomicSelectOp(4) calls TryPoll/OfferDesc(5).prepare which tries to determine
          "affectedNode" but is bound to discover the same Send/ReceiveSelect(3) node that cannot become
          non-first node until this operation completes (there are no insertions to the head of the queue!)
          We have not yet decided to complete this operation, but we cannot ever decide to complete this operation
          on any other node but Send/ReceiveSelect(3), so it is now safe to perform the next step.
       9. PairSelectOp(7).perform calls PrepareOp(6).finishPrepare which copies PrepareOp(6).affected and PrepareOp(6).next
          to the corresponding TryPoll/OfferDesc(5) fields.
       10. PairSelectOp(7).perform calls AtomicSelect(4).decide to reach consensus on successful completion of this
          operation. This consensus is important in light of dead-lock resolution algorithm, because a stale helper
          could have stumbled upon a higher-numbered atomic operation and had decided to abort this atomic operation,
          reaching decision on RETRY_ATOMIC status of it. We cannot proceed with completion in this case and must abort,
          all objects including AtomicSelectOp(4) will be dropped, reverting all the three updated pointers to
          their original values and atomic operation will retry from scratch.
       11. NOW WITH SUCCESSFUL UPDATE OF AtomicSelectOp(4).consensus to null THE RENDEZVOUS IS COMMITTED. The rest
           of the code proceeds to update:
           - SelectBuilderImpl(1).state to TryPoll/OfferDesc(5) so that late helpers would know that we have
             already successfully completed rendezvous.
           - Send/ReceiveSelect(3).next to Removed(next) so that this node becomes marked as removed.
           - SelectBuilderImpl(2).state to null to mark this select instance as selected.

       Note, that very late helper may try to perform this AtomicSelectOp(4) when it is already completed.
       It can proceed as far as finding affected node, creating PrepareOp, installing this new PrepareOp into the
       node's next pointer, but PrepareOp.perform checks that AtomicSelectOp(4) is already decided and undoes all
       the preparations.
     */

    // it is just like plain trySelect, but support idempotent start
    // Returns RESUME_TOKEN | RETRY_ATOMIC | null (when already selected)
    override fun trySelectOther(otherOp: PrepareOp?): Any? {
        _state.loop { state -> // lock-free loop on state
            when {
                // Found initial state (not selected yet) -- try to make it selected
                state === NOT_SELECTED -> {
                    if (otherOp == null) {
                        // regular trySelect -- just mark as select
                        if (!_state.compareAndSet(NOT_SELECTED, null)) return@loop
                    } else {
                        // Rendezvous with another select instance -- install PairSelectOp
                        val pairSelectOp = PairSelectOp(otherOp)
                        if (!_state.compareAndSet(NOT_SELECTED, pairSelectOp)) return@loop
                        val decision = pairSelectOp.perform(this)
                        if (decision !== null) return decision
                    }
                    doAfterSelect()
                    return RESUME_TOKEN
                }
                state is OpDescriptor -> { // state is either AtomicSelectOp or PairSelectOp
                    // Found descriptor of ongoing operation while working in the context of other select operation
                    if (otherOp != null) {
                        val otherAtomicOp = otherOp.atomicOp
                        when {
                            // It is the same select instance
                            otherAtomicOp is AtomicSelectOp && otherAtomicOp.impl === this -> {
                                /*
                                 * We cannot do state.perform(this) here and "help" it since it is the same
                                 * select and we'll get StackOverflowError.
                                 * See https://github.com/Kotlin/kotlinx.coroutines/issues/1411
                                 * We cannot support this because select { ... } is an expression and its clauses
                                 * have a result that shall be returned from the select.
                                 */
                                error("Cannot use matching select clauses on the same object")
                            }
                            // The other select (that is trying to proceed) had started earlier
                            otherAtomicOp.isEarlierThan(state) -> {
                                /**
                                 * Abort to prevent deadlock by returning a failure to it.
                                 * See https://github.com/Kotlin/kotlinx.coroutines/issues/504
                                 * The other select operation will receive a failure and will restart itself with a
                                 * larger sequence number. This guarantees obstruction-freedom of this algorithm.
                                 */
                                return RETRY_ATOMIC
                            }
                        }
                    }
                    // Otherwise (not a special descriptor)
                    state.perform(this) // help it
                }
                // otherwise -- already selected
                otherOp == null -> return null // already selected
                state === otherOp.desc -> return RESUME_TOKEN // was selected with this marker
                else -> return null // selected with different marker
            }
        }
    }

    // The very last step of rendezvous between two select operations
    private class PairSelectOp(
        @JvmField val otherOp: PrepareOp
    ) : OpDescriptor() {
        override fun perform(affected: Any?): Any? {
            val impl = affected as SelectBuilderImpl<*>
            // here we are definitely not going to RETRY_ATOMIC, so
            // we must finish preparation of another operation before attempting to reach decision to select
            otherOp.finishPrepare()
            val decision = otherOp.atomicOp.decide(null) // try decide for success of operation
            val update: Any = if (decision == null) otherOp.desc else NOT_SELECTED
            impl._state.compareAndSet(this, update)
            return decision
        }

        override val atomicOp: AtomicOp<*>?
            get() = otherOp.atomicOp
    }

    override fun performAtomicTrySelect(desc: AtomicDesc): Any? =
        AtomicSelectOp(this, desc).perform(null)

    override fun toString(): String = "SelectInstance(state=${_state.value}, result=${_result.value})"

    private class AtomicSelectOp(
        @JvmField val impl: SelectBuilderImpl<*>,
        @JvmField val desc: AtomicDesc
    ) : AtomicOp<Any?>() {
        // all select operations are totally ordered by their creating time using selectOpSequenceNumber
        override val opSequence = selectOpSequenceNumber.next()

        init {
            desc.atomicOp = this
        }

        override fun prepare(affected: Any?): Any? {
            // only originator of operation makes preparation move of installing descriptor into this selector's state
            // helpers should never do it, or risk ruining progress when they come late
            if (affected == null) {
                // we are originator (affected reference is not null if helping)
                prepareSelectOp()?.let { return it }
            }
            try {
                return desc.prepare(this)
            } catch (e: Throwable) {
                // undo prepareSelectedOp on crash (for example if IllegalStateException is thrown)
                if (affected == null) undoPrepare()
                throw e
            }
        }

        override fun complete(affected: Any?, failure: Any?) {
            completeSelect(failure)
            desc.complete(this, failure)
        }

        private fun prepareSelectOp(): Any? {
            impl._state.loop { state ->
                when {
                    state === this -> return null // already in progress
                    state is OpDescriptor -> state.perform(impl) // help
                    state === NOT_SELECTED -> {
                        if (impl._state.compareAndSet(NOT_SELECTED, this))
                            return null // success
                    }
                    else -> return ALREADY_SELECTED
                }
            }
        }

        // reverts the change done by prepareSelectedOp
        private fun undoPrepare() {
            impl._state.compareAndSet(this, NOT_SELECTED)
        }

        private fun completeSelect(failure: Any?) {
            val selectSuccess = failure == null
            val update = if (selectSuccess) null else NOT_SELECTED
            if (impl._state.compareAndSet(this, update)) {
                if (selectSuccess)
                    impl.doAfterSelect()
            }
        }

        override fun toString(): String = "AtomicSelectOp(sequence=$opSequence)"
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
            if (trySelect())
                block.startCoroutineUnintercepted(completion)
            return
        }
        val action = Runnable {
            // todo: we could have replaced startCoroutine with startCoroutineUndispatched
            // But we need a way to know that Delay.invokeOnTimeout had used the right thread
            if (trySelect())
                block.startCoroutineCancellable(completion) // shall be cancellable while waits for dispatch
        }
        disposeOnSelect(context.delay.invokeOnTimeout(timeMillis, action, context))
    }

    private class DisposeNode(
        @JvmField val handle: DisposableHandle
    ) : LockFreeLinkedListNode()
}
