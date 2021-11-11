/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.sync

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*
import kotlin.contracts.*
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
     * Returns `true` if this mutex is locked.
     */
    public val isLocked: Boolean

    /**
     * Tries to lock this mutex, returning `false` if this mutex is already locked.
     *
     * It is recommended to use [withLock] for safety reasons, so that the acquired lock is always
     * released at the end of your critical section, and [unlock] is never invoked before a successful
     * lock acquisition.
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
     * This function can be used in [select] invocation with [onLock] clause.
     * Use [tryLock] to try acquiring the lock without waiting.
     *
     * This function is fair; suspended callers are resumed in first-in-first-out order.
     *
     * It is recommended to use [withLock] for safety reasons, so that the acquired lock is always
     * released at the end of the critical section, and [unlock] is never invoked before a successful
     * lock acquisition.
     *
     * @param owner Optional owner token for debugging. When `owner` is specified (non-null value) and this mutex
     *        is already locked with the same token (same identity), this function throws [IllegalStateException].
     */
    public suspend fun lock(owner: Any? = null)

    /**
     * Clause for [select] expression of [lock] suspending function that selects when the mutex is locked.
     * Additional parameter for the clause in the `owner` (see [lock]) and when the clause is selected
     * the reference to this mutex is passed into the corresponding block.
     *
     * It is recommended to use [withLock] for safety reasons, so that the acquired lock is always
     * released at the end of the critical section, and [unlock] is never invoked before a successful
     * lock acquisition.
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = "Mutex.onLock deprecated without replacement. " +
        "For additional details please refer to #2794")
    public val onLock: SelectClause2<Any?, Mutex>

    /**
     * Checks whether this mutex is locked by the specified owner.
     *
     * @return `true` on mutex lock by owner, `false` if not locker or it is locked by different owner
     */
    public fun holdsLock(owner: Any): Boolean

    /**
     * Unlocks this mutex. Throws [IllegalStateException] if invoked on a mutex that is not locked or
     * was locked with a different owner token (by identity).
     *
     * It is recommended to use [withLock] for safety reasons, so that the acquired lock is always
     * released at the end of the critical section, and [unlock] is never invoked before a successful
     * lock acquisition.
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
    MutexImpl(locked) // TODO: locked with owner?

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


internal class MutexImpl(locked: Boolean) : SemaphoreImpl(1, if (locked) 1 else 0), Mutex {
    private val owner = atomic<Any?>(if (locked) null else NO_OWNER)

    override val isLocked: Boolean get() =
        availablePermits == 0

    override fun holdsLock(owner: Any): Boolean {
        while (true) {
            // Is this mutex locked?
            if (!isLocked) return false
            val curOwner = this.owner.value
            // Wait in a spin-loop until the owner is set
            if (curOwner === NO_OWNER) continue // <-- ATTENTION, BLOCKING PART HERE
            // Check the owner
            return curOwner === owner
        }
    }

    override suspend fun lock(owner: Any?) {
        if (tryLock(owner)) return
        lockSuspend(owner)
    }

    private suspend fun lockSuspend(owner: Any?) = suspendCancellableCoroutineReusable<Unit> { cont ->
        val contWithOwner = CancellableContinuationWithOwner(cont, owner)
        acquire(contWithOwner)
    }

    override fun tryLock(owner: Any?): Boolean =
        if (tryAcquire()) {
            this.owner.value = owner
            true
        } else false

    override fun unlock(owner: Any?) {
        var i = 1
        while (true) {
            // Is this mutex locked?
            check(isLocked) { "This mutex is not locked" }
            // Read the owner, waiting until it is set in a spin-loop if required.
            val curOwner = this.owner.value
            if (curOwner === NO_OWNER) continue // <-- ATTENTION, BLOCKING PART HERE
            i++
            if (i % 1_000 == 0) println("WTF")
            // Check the owner.
            check(curOwner === owner) { "This mutex is locked by $curOwner, but $owner is expected" }
            // Try to clean the owner first. We need to use CAS here to synchronize with concurrent `unlock(..)`-s.
            if (!this.owner.compareAndSet(owner, NO_OWNER)) continue
            // Release the semaphore permit at the end.
            release()
            return
        }
    }

    override val onLock: SelectClause2<Any?, Mutex> get() = SelectClause2Impl(
        objForSelect = this,
        regFunc = MutexImpl::onLockRegFunction as RegistrationFunction,
        processResFunc = MutexImpl::onLockProcessResult as ProcessResultFunction,
    )

    private fun onLockRegFunction(select: SelectInstance<*>, owner: Any?) {
        onAcquire.regFunc(this, SelectInstanceWithOwner(select, owner), owner)
    }

    private fun onLockProcessResult(owner: Any?, result: Any?): Any? {
        onAcquire.processResFunc(this, null, result)
        while (isLocked && this.owner.value === NO_OWNER) {}
        return this
    }

    private inner class SelectInstanceWithOwner<Q>(
        val select: SelectInstance<Q>,
        val owner: Any?
    ) : SelectInstance<Q> by select {
        override fun trySelect(objForSelect: Any, result: Any?): Boolean {
            return select.trySelect(objForSelect, result).also { success ->
                if (success) this@MutexImpl.owner.value = owner
            }
        }

        override fun selectInRegPhase(selectResult: Any?) {
            select.selectInRegPhase(selectResult)
            this@MutexImpl.owner.value = owner
        }
    }

    private inner class CancellableContinuationWithOwner(
        val cont: CancellableContinuation<Unit>,
        val owner: Any?
    ) : CancellableContinuation<Unit> by cont {
        override fun tryResume(value: Unit, idempotent: Any?, onCancellation: ((cause: Throwable) -> Unit)?): Any? {
            val token = cont.tryResume(value, idempotent, onCancellation)
            if (token !== null) this@MutexImpl.owner.value = owner
            return token
        }

        override fun resume(value: Unit, onCancellation: ((cause: Throwable) -> Unit)?) {
            this@MutexImpl.owner.value = owner
            cont.resume(value, onCancellation)
        }
    }
}

@SharedImmutable
private val NO_OWNER = Symbol("NO_OWNER")
