/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.sync

import kotlinx.atomicfu.*
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.internal.*
import kotlinx.coroutines.experimental.intrinsics.*
import kotlinx.coroutines.experimental.selects.*
import kotlin.coroutines.experimental.*

/**
 * Mutual exclusion for coroutines.
 *
 * Mutex has two states: _locked_ and _unlocked_.
 * It is **non-reentrant**, that is invoking [lock] even from the same thread/coroutine that currently holds
 * the lock still suspends the invoker.
 *
 * JVM API note:
 * Memory semantic of the [Mutex] is similar to `synchronized` block on JVM:
 * An unlock on a [Mutex] happens-before every subsequent successful lock on that [Mutex].
 * Unsuccessful call to [tryLock] do not have any memory effects.
 */
public interface Mutex {
    /**
     * Returns `true` when this mutex is locked.
     */
    public val isLocked: Boolean

    /**
     * Tries to lock this mutex, returning `false` if this mutex is already locked.
     *
     * @param owner Optional owner token for debugging. When `owner` is specified (non-null value) and this mutex
     *        is already locked with the same token (same identity), this function throws [IllegalStateException].
     */
    public fun tryLock(owner: Any? = null): Boolean

    /**
     * Locks this mutex, suspending caller while the mutex is locked.
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this
     * function is suspended, this function immediately resumes with [CancellationException].
     *
     * *Cancellation of suspended lock invocation is atomic* -- when this function
     * throws [CancellationException] it means that the mutex was not locked.
     * As a side-effect of atomic cancellation, a thread-bound coroutine (to some UI thread, for example) may
     * continue to execute even after it was cancelled from the same thread in the case when this lock operation
     * was already resumed and the continuation was posted for execution to the thread's queue.
     *
     * Note, that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     *
     * This function can be used in [select] invocation with [onLock] clause.
     * Use [tryLock] to try acquire lock without waiting.
     *
     * This function is fair; suspended callers are resumed in first-in-first-out order.
     *
     * @param owner Optional owner token for debugging. When `owner` is specified (non-null value) and this mutex
     *        is already locked with the same token (same identity), this function throws [IllegalStateException].
     */
    public suspend fun lock(owner: Any? = null)

    /**
     * Clause for [select] expression of [lock] suspending function that selects when the mutex is locked.
     * Additional parameter for the clause in the `owner` (see [lock]) and when the clause is selected
     * the reference to this mutex is passed into the corresponding block.
     */
    public val onLock: SelectClause2<Any?, Mutex>

    /**
     * Checks mutex locked by owner
     *
     * @return `true` on mutex lock by owner, `false` if not locker or it is locked by different owner
     */
    public fun holdsLock(owner: Any): Boolean

        /**
     * Unlocks this mutex. Throws [IllegalStateException] if invoked on a mutex that is not locked.
     *
     * @param owner Optional owner token for debugging. When `owner` is specified (non-null value) and this mutex
     *        was locked with the different token (by identity), this function throws [IllegalStateException].
     */
    public fun unlock(owner: Any? = null)
}

/**
 * Creates new [Mutex] instance.
 * The mutex created is fair: lock is granted in first come, first served order.
 *
 * @param locked initial state of the mutex.
 */
@Suppress("FunctionName")
public fun Mutex(locked: Boolean = false): Mutex =
    MutexImpl(locked)

/**
 * Executes the given [action] under this mutex's lock.
 *
 * @param owner Optional owner token for debugging.
 *
 * @return the return value of the action.
 */
public suspend inline fun <T> Mutex.withLock(owner: Any? = null, action: () -> T): T {
    lock(owner)
    try {
        return action()
    } finally {
        unlock(owner)
    }
}

/**
 * @suppress: **Deprecated**: binary compatibility with old code
 */
@Deprecated("binary compatibility with old code", level = DeprecationLevel.HIDDEN)
public suspend fun <T> Mutex.withLock(owner: Any? = null, action: suspend () -> T): T =
    withLock(owner) { action() }

/**
 * @suppress: **Deprecated**: Use [withLock]
 */
@Deprecated("Use `withLock(owner, action)", level = DeprecationLevel.HIDDEN)
public suspend fun <T> Mutex.withLock(action: suspend () -> T): T =
    withLock { action() }

/**
 * @suppress: **Deprecated**: Use [withLock]
 */
@Deprecated("Use `withLock`", replaceWith = ReplaceWith("withLock(action)"))
public suspend fun <T> Mutex.withMutex(action: suspend () -> T): T =
    withLock { action() }

private val LOCK_FAIL = Symbol("LOCK_FAIL")
private val ENQUEUE_FAIL = Symbol("ENQUEUE_FAIL")
private val UNLOCK_FAIL = Symbol("UNLOCK_FAIL")
private val SELECT_SUCCESS = Symbol("SELECT_SUCCESS")
private val LOCKED = Symbol("LOCKED")
private val UNLOCKED = Symbol("UNLOCKED")
private val RESUME_QUIESCENT = Symbol("RESUME_QUIESCENT")
private val RESUME_ACTIVE = Symbol("RESUME_ACTIVE")

private val EmptyLocked = Empty(LOCKED)
private val EmptyUnlocked = Empty(UNLOCKED)

private class Empty(
    @JvmField val locked: Any
) {
    override fun toString(): String = "Empty[$locked]"
}

internal class MutexImpl(locked: Boolean) : Mutex, SelectClause2<Any?, Mutex> {
    // State is: Empty | LockedQueue | OpDescriptor
    // shared objects while we have no waiters
    private val _state = atomic<Any?>(if (locked) EmptyLocked else EmptyUnlocked)

    // resumeNext is: RESUME_QUIESCENT | RESUME_ACTIVE | ResumeReq
    private val _resumeNext = atomic<Any>(RESUME_QUIESCENT)

    public override val isLocked: Boolean get() {
        _state.loop { state ->
            when (state) {
                is Empty -> return state.locked !== UNLOCKED
                is LockedQueue -> return true
                is OpDescriptor -> state.perform(this) // help
                else -> error("Illegal state $state")
            }
        }
    }

    // for tests ONLY
    internal val isLockedEmptyQueueState: Boolean get() {
        val state = _state.value
        return state is LockedQueue && state.isEmpty
    }

    public override fun tryLock(owner: Any?): Boolean {
        _state.loop { state ->
            when (state) {
                is Empty -> {
                    if (state.locked !== UNLOCKED) return false
                    val update = if (owner == null) EmptyLocked else Empty(
                        owner
                    )
                    if (_state.compareAndSet(state, update)) return true
                }
                is LockedQueue -> {
                    check(state.owner !== owner) { "Already locked by $owner" }
                    return false
                }
                is OpDescriptor -> state.perform(this) // help
                else -> error("Illegal state $state")
            }
        }
    }

    public override suspend fun lock(owner: Any?) {
        // fast-path -- try lock
        if (tryLock(owner)) return
        // slow-path -- suspend
        return lockSuspend(owner)
    }

    private suspend fun lockSuspend(owner: Any?) = suspendAtomicCancellableCoroutine<Unit>(holdCancellability = true) sc@ { cont ->
        val waiter = LockCont(owner, cont)
        _state.loop { state ->
            when (state) {
                is Empty -> {
                    if (state.locked !== UNLOCKED) {  // try upgrade to queue & retry
                        _state.compareAndSet(state, LockedQueue(state.locked))
                    } else {
                        // try lock
                        val update = if (owner == null) EmptyLocked else Empty(owner)
                        if (_state.compareAndSet(state, update)) { // locked
                            cont.resume(Unit)
                            return@sc
                        }
                    }
                }
                is LockedQueue -> {
                    val curOwner = state.owner
                    check(curOwner !== owner) { "Already locked by $owner" }
                    if (state.addLastIf(waiter, { _state.value === state })) {
                        // added to waiter list!
                        cont.initCancellability() // make it properly cancellable
                        cont.removeOnCancellation(waiter)
                        return@sc
                    }
                }
                is OpDescriptor -> state.perform(this) // help
                else -> error("Illegal state $state")
            }
        }
    }

    override val onLock: SelectClause2<Any?, Mutex>
        get() = this

    // registerSelectLock
    @Suppress("PARAMETER_NAME_CHANGED_ON_OVERRIDE")
    override fun <R> registerSelectClause2(select: SelectInstance<R>, owner: Any?, block: suspend (Mutex) -> R) {
        while (true) { // lock-free loop on state
            if (select.isSelected) return
            val state = _state.value
            when (state) {
                is Empty -> {
                    if (state.locked !== UNLOCKED) { // try upgrade to queue & retry
                        _state.compareAndSet(state, LockedQueue(state.locked))
                    } else {
                        // try lock
                        val failure = select.performAtomicTrySelect(TryLockDesc(this, owner))
                        when {
                            failure == null -> { // success
                                block.startCoroutineUndispatched(receiver = this, completion = select.completion)
                                return
                            }
                            failure === ALREADY_SELECTED -> return // already selected -- bail out
                            failure === LOCK_FAIL -> {} // retry
                            else -> error("performAtomicTrySelect(TryLockDesc) returned $failure")
                        }
                    }
                }
                is LockedQueue -> {
                    check(state.owner !== owner) { "Already locked by $owner" }
                    val enqueueOp = TryEnqueueLockDesc(this, owner, state, select, block)
                    val failure = select.performAtomicIfNotSelected(enqueueOp)
                    when {
                        failure == null -> { // successfully enqueued
                            select.disposeOnSelect(enqueueOp.node)
                            return
                        }
                        failure === ALREADY_SELECTED -> return // already selected -- bail out
                        failure === ENQUEUE_FAIL -> {} // retry
                        else -> error("performAtomicIfNotSelected(TryEnqueueLockDesc) returned $failure")
                    }
                }
                is OpDescriptor -> state.perform(this) // help
                else -> error("Illegal state $state")
            }
        }
    }

    private class TryLockDesc(
        @JvmField val mutex: MutexImpl,
        @JvmField val owner: Any?
    ) : AtomicDesc() {
        // This is Harris's RDCSS (Restricted Double-Compare Single Swap) operation
        private inner class PrepareOp(private val op: AtomicOp<*>) : OpDescriptor() {
            override fun perform(affected: Any?): Any? {
                val update: Any = if (op.isDecided) EmptyUnlocked else op // restore if was already decided
                (affected as MutexImpl)._state.compareAndSet(this, update)
                return null // ok
            }
        }

        override fun prepare(op: AtomicOp<*>): Any? {
            val prepare = PrepareOp(op)
            if (!mutex._state.compareAndSet(EmptyUnlocked, prepare)) return LOCK_FAIL
            return prepare.perform(mutex)
        }

        override fun complete(op: AtomicOp<*>, failure: Any?) {
            val update = if (failure != null) EmptyUnlocked else {
                if (owner == null) EmptyLocked else Empty(owner)
            }
            mutex._state.compareAndSet(op, update)
        }
    }

    private class TryEnqueueLockDesc<R>(
        @JvmField val mutex: MutexImpl,
        owner: Any?,
        queue: LockedQueue,
        select: SelectInstance<R>,
        block: suspend (Mutex) -> R
    ) : AddLastDesc<LockSelect<R>>(queue, LockSelect(owner, mutex, select, block)) {
        override fun onPrepare(affected: LockFreeLinkedListNode, next: LockFreeLinkedListNode): Any? {
            if (mutex._state.value !== queue) return ENQUEUE_FAIL
            return super.onPrepare(affected, next)
        }
    }

    public override fun holdsLock(owner: Any) =
            _state.value.let { state ->
                when (state) {
                    is Empty -> state.locked === owner
                    is LockedQueue -> state.owner === owner
                    else -> false
                }
            }

    public override fun unlock(owner: Any?) {
        _state.loop { state ->
            when (state) {
                is Empty -> {
                    if (owner == null)
                        check(state.locked !== UNLOCKED) { "Mutex is not locked" }
                    else
                        check(state.locked === owner) { "Mutex is locked by ${state.locked} but expected $owner" }
                    if (_state.compareAndSet(state, EmptyUnlocked)) return
                }
                is OpDescriptor -> state.perform(this)
                is LockedQueue -> {
                    if (owner != null)
                        check(state.owner === owner) { "Mutex is locked by ${state.owner} but expected $owner" }
                    val waiter = state.removeFirstOrNull()
                    if (waiter == null) {
                        val op = UnlockOp(state)
                        if (_state.compareAndSet(state, op) && op.perform(this) == null) return
                    } else {
                        val token = (waiter as LockWaiter).tryResumeLockWaiter()
                        if (token != null) {
                            // successfully resumed waiter that now is holding the lock
                            // we must immediately transfer ownership to the next waiter, because this coroutine
                            // might try to lock it again after unlock returns do to StackOverflow avoidance code
                            // and its attempts to take a lock must be queued.
                            state.owner = waiter.owner ?: LOCKED
                            // StackOverflow avoidance code
                            if (startResumeNext(waiter, token)) {
                                waiter.completeResumeLockWaiter(token)
                                finishResumeNext()
                            }
                            return
                        }
                    }
                }
                else -> error("Illegal state $state")
            }
        }
    }

    private class ResumeReq(
        @JvmField val waiter: LockWaiter,
        @JvmField val token: Any
    )

    private fun startResumeNext(waiter: LockWaiter, token: Any): Boolean {
        _resumeNext.loop { resumeNext ->
            when {
                resumeNext === RESUME_QUIESCENT -> {
                    // this is never concurrent, because only one thread is holding mutex and trying to resume
                    // next waiter, so no need to CAS here
                    _resumeNext.value = RESUME_ACTIVE
                    return true
                }
                resumeNext === RESUME_ACTIVE ->
                    if (_resumeNext.compareAndSet(resumeNext, ResumeReq(waiter, token))) return false
                else -> error("Cannot happen")
            }
        }
    }

    private fun finishResumeNext() {
        // also a resumption loop to fulfill requests of inner resume invokes
        _resumeNext.loop { resumeNext ->
            when {
                resumeNext === RESUME_ACTIVE ->
                    if (_resumeNext.compareAndSet(resumeNext, RESUME_QUIESCENT)) return
                resumeNext is ResumeReq -> {
                    // this is never concurrently, only one thread is finishing, so no need to CAS here
                    _resumeNext.value = RESUME_ACTIVE
                    resumeNext.waiter.completeResumeLockWaiter(resumeNext.token)
                }
                else -> error("Cannot happen")
            }
        }
    }

    override fun toString(): String {
        _state.loop { state ->
            when (state) {
                is Empty -> return "Mutex[${state.locked}]"
                is OpDescriptor -> state.perform(this)
                is LockedQueue -> return "Mutex[${state.owner}]"
                else -> error("Illegal state $state")
            }
        }
    }

    private class LockedQueue(
        @JvmField var owner: Any
    ) : LockFreeLinkedListHead() {
        override fun toString(): String = "LockedQueue[$owner]"
    }

    private abstract class LockWaiter(
        @JvmField val owner: Any?
    ) : LockFreeLinkedListNode(), DisposableHandle {
        final override fun dispose() { remove() }
        abstract fun tryResumeLockWaiter(): Any?
        abstract fun completeResumeLockWaiter(token: Any)
    }

    private class LockCont(
        owner: Any?,
        @JvmField val cont: CancellableContinuation<Unit>
    ) : LockWaiter(owner) {
        override fun tryResumeLockWaiter() = cont.tryResume(Unit)
        override fun completeResumeLockWaiter(token: Any) = cont.completeResume(token)
        override fun toString(): String = "LockCont[$owner, $cont]"
    }

    private class LockSelect<R>(
        owner: Any?,
        @JvmField val mutex: Mutex,
        @JvmField val select: SelectInstance<R>,
        @JvmField val block: suspend (Mutex) -> R
    ) : LockWaiter(owner) {
        override fun tryResumeLockWaiter(): Any? = if (select.trySelect(null)) SELECT_SUCCESS else null
        override fun completeResumeLockWaiter(token: Any) {
            check(token === SELECT_SUCCESS)
            block.startCoroutine(receiver = mutex, completion = select.completion)
        }
        override fun toString(): String = "LockSelect[$owner, $mutex, $select]"
    }

    // atomic unlock operation that checks that waiters queue is empty
    private class UnlockOp(
        @JvmField val queue: LockedQueue
    ) : OpDescriptor() {
        override fun perform(affected: Any?): Any? {
            /*
               Note: queue cannot change while this UnlockOp is in progress, so all concurrent attempts to
               make a decision will reach it consistently. It does not matter what is a proposed
               decision when this UnlockOp is no longer active, because in this case the following CAS
               will fail anyway.
             */
            val success = queue.isEmpty
            val update: Any = if (success) EmptyUnlocked else queue
            (affected as MutexImpl)._state.compareAndSet(this@UnlockOp, update)
            /*
                `perform` invocation from the original `unlock` invocation may be coming too late, when
                some other thread had already helped to complete it (either successfully or not).
                That operation was unsuccessful if `state` was restored to this `queue` reference and
                that is what is being checked below.
             */
            return if (affected._state.value === queue) UNLOCK_FAIL else null
        }
    }
}
