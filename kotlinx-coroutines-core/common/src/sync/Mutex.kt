/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.sync

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*

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
// TODO mention that lock/unlock have two phases: synchronization + setting/resetting the owner
public interface Mutex {
    /**
     * Returns `true` when this mutex is locked.
     */
    public val isLocked: Boolean

    /**
     * Tries to lock this mutex, returning `false` if it is already locked.
     *
     * @param owner Optional owner token for debugging. When `owner` is specified (non-null value),
     *              the subsequent [unlock] invocation should use it as a parameter,
     *              trowing [IllegalStateException] if the owners do not coincide.
     */
    public fun tryLock(owner: Any? = null): Boolean

    /**
     * Locks this mutex, suspending the caller if the mutex is locked.
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
     * Note that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     *
     * This function can be used in [select] invocation with [onLock] clause.
     * Use [tryLock] to try acquire lock without waiting.
     *
     * This function is fair; suspended callers are resumed in first-come-first-served order.
     *
     * @param owner Optional owner token for debugging. When `owner` is specified (non-null value),
     *              the subsequent [unlock] invocation should use it as a parameter,
     *              trowing [IllegalStateException] if the owners do not coincide.
     */
    public suspend fun lock(owner: Any? = null)

    /**
     * Clause for [select] expression of [lock] suspending function that selects when the mutex is locked.
     * Additional parameter for the clause in the `owner` (see [lock]) and when the clause is selected
     * the reference to this mutex is passed into the corresponding block.
     */
    public val onLock: SelectClause2<Any?, Mutex>

    /**
     * Checks whether this mutex is locked by the specified owner.
     *
     * @return `true` if this mutex is locked by the specified owner,
     * or `false` if it is either locked by another one or is in the _unlocked_ state.
     */
    public fun holdsLock(owner: Any): Boolean

    /**
     * Unlocks this mutex. Throws [IllegalStateException] if this mutex is in the _unlocked_ state or it is locked with
     * another token; in other words, [holdsLock] should return `true` at the point of this function invocation.
     *
     * @param owner Optional owner token for debugging. When `owner` is specified (non-null value) and this mutex
     *        is locked with another token (comparing by identity), this function throws [IllegalStateException].
     */
    public fun unlock(owner: Any? = null)
}

/**
 * Creates a new [Mutex] instance. The returning mutex is fair:
 * suspended [lock] callers are resumed in first-come-first-served order.
 *
 * @param locked specifies whether the returning mutex should be in the _locked_ state or not.
 */
@Suppress("FunctionName")
public fun Mutex(locked: Boolean = false): Mutex =
    MutexImpl(locked)

/**
 * Executes the specified [action] guarding by this mutex.
 *
 * @return the [action] result.
 */
// TODO incompatible change here: the `owner` parameter is removed
public suspend inline fun <T> Mutex.withLock(action: () -> T): T {
    lock()
    try {
        return action()
    } finally {
        unlock()
    }
}

private class MutexImpl(locked: Boolean) : SemaphoreImpl(permits = 1, acquiredPermits = if (locked) 1 else 0), Mutex {
    private val owner = atomic<Any?>(null)

    override val isLocked: Boolean get() = availablePermits == 0
    override fun holdsLock(owner: Any): Boolean = this.owner.value === owner

    override fun tryLock(owner: Any?): Boolean {
        return if (tryAcquire()) {
            this.owner.value = owner
            true
        } else false
    }

    public override suspend fun lock(owner: Any?) {
        acquire()
        this.owner.value = owner
    }

    override fun unlock(owner: Any?) {
        if (!this.owner.compareAndSet(owner, null)) {
            // Please note, that this owner read can be incorrect; however, it is totally fine for debugging.
            error("Mutex is locked by ${this.owner.value} but expected $owner")
        }
        release()
    }

    override val invalidReleaseMessage: String
        get() = "The number of `unlock` invocations cannot be greater than the number of lock acquisitions; this mutex is broken"

    override val onLock: SelectClause2<Any?, Mutex> get() = TODO("Waiting for a new `select` algorithm")
}