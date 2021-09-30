/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.sync

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.intrinsics.*
import kotlinx.coroutines.selects.*
import kotlin.contracts.*
import kotlin.jvm.*
import kotlin.native.concurrent.*

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
     * There is a **prompt cancellation guarantee**. If the job was cancelled while this function was
     * suspended, it will not resume successfully. See [suspendCancellableCoroutine] documentation for low-level details.
     * This function releases the lock if it was already acquired by this function before the [CancellationException]
     * was thrown.
     *
     * Note that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     *
     * Use [tryLock] to try acquiring a lock without waiting.
     *
     * This function is fair; suspended callers are resumed in first-in-first-out order.
     *
     * @param owner Optional owner token for debugging. When `owner` is specified (non-null value) and this mutex
     *        is already locked with the same token (same identity), this function throws [IllegalStateException].
     */
    public suspend fun lock(owner: Any? = null)

    /**
     * Deprecated for removal without built-in replacement.
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = "Mutex.onLock deprecated without replacement. " +
        "For additional details please refer to #2794")
    public val onLock: SelectClause2<Any?, Mutex>

    /**
     * Checks mutex locked by owner
     *
     * @return `true` on mutex lock by owner, `false` if not locker or it is locked by different owner
     */
    public fun holdsLock(owner: Any): Boolean

    /**
     * Unlocks this mutex. Throws [IllegalStateException] if invoked on a mutex that is not locked or
     * was locked with a different owner token (by identity).
     *
     * @param owner Optional owner token for debugging. When `owner` is specified (non-null value) and this mutex
     *        was locked with the different token (by identity), this function throws [IllegalStateException].
     */
    public fun unlock(owner: Any? = null)
}

/**
 * Creates a [Mutex] instance.
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
 * @param owner Optional owner token for debugging. When `owner` is specified (non-null value) and this mutex
 *        is already locked with the same token (same identity), this function throws [IllegalStateException].
 *
 * @return the return value of the action.
 */
@OptIn(ExperimentalContracts::class)
public suspend inline fun <T> Mutex.withLock(owner: Any? = null, action: () -> T): T {
    contract { 
        callsInPlace(action, InvocationKind.EXACTLY_ONCE)
    }

    lock(owner)
    try {
        return action()
    } finally {
        unlock(owner)
    }
}

@SharedImmutable
private val LOCK_FAIL = Symbol("LOCK_FAIL")
@SharedImmutable
private val UNLOCK_FAIL = Symbol("UNLOCK_FAIL")
@SharedImmutable
private val LOCKED = Symbol("LOCKED")
@SharedImmutable
private val UNLOCKED = Symbol("UNLOCKED")

@SharedImmutable
private val EMPTY_LOCKED = Empty(LOCKED)
@SharedImmutable
private val EMPTY_UNLOCKED = Empty(UNLOCKED)

private class Empty(
    @JvmField val locked: Any
) {
    override fun toString(): String = "Empty[$locked]"
}

internal class MutexImpl(locked: Boolean) : Mutex, SelectClause2<Any?, Mutex> {
    // State is: Empty | LockedQueue | OpDescriptor
    // shared objects while we have no waiters
    private val _state = atomic<Any?>(if (locked) EMPTY_LOCKED else EMPTY_UNLOCKED)

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
                    val update = if (owner == null) EMPTY_LOCKED else Empty(
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

    private suspend fun lockSuspend(owner: Any?) = suspendCancellableCoroutineReusable<Unit> sc@ { cont ->
        var waiter = LockCont(owner, cont)
        _state.loop { state ->
            when (state) {
                is Empty -> {
                    if (state.locked !== UNLOCKED) {  // try upgrade to queue & retry
                        _state.compareAndSet(state, LockedQueue(state.locked))
                    } else {
                        // try lock
                        val update = if (owner == null) EMPTY_LOCKED else Empty(owner)
                        if (_state.compareAndSet(state, update)) { // locked
                            // TODO implement functional type in LockCont as soon as we get rid of legacy JS
                            cont.resume(Unit) { unlock(owner) }
                            return@sc
                        }
                    }
                }
                is LockedQueue -> {
                    val curOwner = state.owner
                    check(curOwner !== owner) { "Already locked by $owner" }

                    state.addLast(waiter)
                    /*
                     * If the state has been changed while we were adding the waiter,
                     * it means that 'unlock' has taken it and _either_ resumed it successfully or just overwritten.
                     * To rendezvous that, we try to "invalidate" our node and go for retry.
                     *
                     * Node has to be re-instantiated as we do not support node re-adding, even to
                     * another list
                     */
                    if (_state.value === state || !waiter.take()) {
                        // added to waiter list
                        cont.removeOnCancellation(waiter)
                        return@sc
                    }

                    waiter = LockCont(owner, cont)
                    return@loop
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
            when (val state = _state.value) {
                is Empty -> {
                    if (state.locked !== UNLOCKED) { // try upgrade to queue & retry
                        _state.compareAndSet(state, LockedQueue(state.locked))
                    } else {
                        // try lock
                        val failure = select.performAtomicTrySelect(TryLockDesc(this, owner))
                        when {
                            failure == null -> { // success
                                block.startCoroutineUnintercepted(receiver = this, completion = select.completion)
                                return
                            }
                            failure === ALREADY_SELECTED -> return // already selected -- bail out
                            failure === LOCK_FAIL -> {} // retry
                            failure === RETRY_ATOMIC -> {} // retry
                            else -> error("performAtomicTrySelect(TryLockDesc) returned $failure")
                        }
                    }
                }
                is LockedQueue -> {
                    check(state.owner !== owner) { "Already locked by $owner" }
                    val node = LockSelect(owner, select, block)
                    /*
                     * If the state has been changed while we were adding the waiter,
                     * it means that 'unlock' has taken it and _either_ resumed it successfully or just overwritten.
                     * To rendezvous that, we try to "invalidate" our node and go for retry.
                     *
                     * Node has to be re-instantiated as we do not support node re-adding, even to
                     * another list
                     */
                    state.addLast(node)
                    if (_state.value === state || !node.take()) {
                        // added to waiter list
                        select.disposeOnSelect(node)
                        return
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
        private inner class PrepareOp(override val atomicOp: AtomicOp<*>) : OpDescriptor() {
            override fun perform(affected: Any?): Any? {
                val update: Any = if (atomicOp.isDecided) EMPTY_UNLOCKED else atomicOp // restore if was already decided
                (affected as MutexImpl)._state.compareAndSet(this, update)
                return null // ok
            }
        }

        override fun prepare(op: AtomicOp<*>): Any? {
            val prepare = PrepareOp(op)
            if (!mutex._state.compareAndSet(EMPTY_UNLOCKED, prepare)) return LOCK_FAIL
            return prepare.perform(mutex)
        }

        override fun complete(op: AtomicOp<*>, failure: Any?) {
            val update = if (failure != null) EMPTY_UNLOCKED else {
                if (owner == null) EMPTY_LOCKED else Empty(owner)
            }
            mutex._state.compareAndSet(op, update)
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

    override fun unlock(owner: Any?) {
        _state.loop { state ->
            when (state) {
                is Empty -> {
                    if (owner == null)
                        check(state.locked !== UNLOCKED) { "Mutex is not locked" }
                    else
                        check(state.locked === owner) { "Mutex is locked by ${state.locked} but expected $owner" }
                    if (_state.compareAndSet(state, EMPTY_UNLOCKED)) return
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
                        if ((waiter as LockWaiter).tryResumeLockWaiter()) {
                            state.owner = waiter.owner ?: LOCKED
                            waiter.completeResumeLockWaiter()
                            return
                        }
                    }
                }
                else -> error("Illegal state $state")
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

    private abstract inner class LockWaiter(
        @JvmField val owner: Any?
    ) : LockFreeLinkedListNode(), DisposableHandle {
        private val isTaken = atomic<Boolean>(false)
        fun take(): Boolean = isTaken.compareAndSet(false, true)
        final override fun dispose() { remove() }
        abstract fun tryResumeLockWaiter(): Boolean
        abstract fun completeResumeLockWaiter()
    }

    private inner class LockCont(
        owner: Any?,
        private val cont: CancellableContinuation<Unit>
    ) : LockWaiter(owner) {

        override fun tryResumeLockWaiter(): Boolean {
            if (!take()) return false
            return cont.tryResume(Unit, idempotent = null) {
                // if this continuation gets cancelled during dispatch to the caller, then release the lock
                unlock(owner)
            } != null
        }

        override fun completeResumeLockWaiter() = cont.completeResume(RESUME_TOKEN)
        override fun toString(): String = "LockCont[$owner, ${cont}] for ${this@MutexImpl}"
    }

    private inner class LockSelect<R>(
        owner: Any?,
        @JvmField val select: SelectInstance<R>,
        @JvmField val block: suspend (Mutex) -> R
    ) : LockWaiter(owner) {
        override fun tryResumeLockWaiter(): Boolean = take() && select.trySelect()
        override fun completeResumeLockWaiter() {
            block.startCoroutineCancellable(receiver = this@MutexImpl, completion = select.completion) {
                // if this continuation gets cancelled during dispatch to the caller, then release the lock
                unlock(owner)
            }
        }
        override fun toString(): String = "LockSelect[$owner, $select] for ${this@MutexImpl}"
    }

    // atomic unlock operation that checks that waiters queue is empty
    private class UnlockOp(
        @JvmField val queue: LockedQueue
    ) : AtomicOp<MutexImpl>() {
        override fun prepare(affected: MutexImpl): Any? =
            if (queue.isEmpty) null else UNLOCK_FAIL

        override fun complete(affected: MutexImpl, failure: Any?) {
            val update: Any = if (failure == null) EMPTY_UNLOCKED else queue
            affected._state.compareAndSet(this, update)
        }
    }
}
