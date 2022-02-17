/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.sync

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.contracts.*
import kotlin.coroutines.*
import kotlin.math.*

/**
 * A counting semaphore for coroutines that logically maintains a number of available permits.
 * Each [acquire] takes a single permit or suspends until it is available.
 * Each [release] adds a permit, potentially releasing a suspended acquirer.
 * Semaphore is fair and maintains a FIFO order of acquirers.
 *
 * Semaphores are mostly used to limit the number of coroutines that have an access to particular resource.
 * Semaphore with `permits = 1` is essentially a [Mutex].
 **/
public interface Semaphore {
    /**
     * Returns the current number of permits available in this semaphore.
     */
    public val availablePermits: Int

    /**
     * Acquires a permit from this semaphore, suspending until one is available.
     * All suspending acquirers are processed in first-in-first-out (FIFO) order.
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this
     * function is suspended, this function immediately resumes with [CancellationException].
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this
     * function is suspended, this function immediately resumes with [CancellationException].
     * There is a **prompt cancellation guarantee**. If the job was cancelled while this function was
     * suspended, it will not resume successfully. See [suspendCancellableCoroutine] documentation for low-level details.
     * This function releases the semaphore if it was already acquired by this function before the [CancellationException]
     * was thrown.
     *
     * Note, that this function does not check for cancellation when it does not suspend.
     * Use [CoroutineScope.isActive] or [CoroutineScope.ensureActive] to periodically
     * check for cancellation in tight loops if needed.
     *
     * Use [tryAcquire] to try acquire a permit of this semaphore without suspension.
     *
     * It is recommended to use [withPermit] for safety reasons, so that the acquired permit is always
     * released at the end of your critical section and [release] is never invoked before a successful
     * permit acquisition.
     */
    public suspend fun acquire()

    /**
     * Tries to acquire a permit from this semaphore without suspension.
     *
     * It is recommended to use [withPermit] for safety reasons, so that the acquired permit is always
     * released at the end of your critical section and [release] is never invoked before a successful
     * permit acquisition.
     *
     * @return `true` if a permit was acquired, `false` otherwise.
     */
    public fun tryAcquire(): Boolean

    /**
     * Releases a permit, returning it into this semaphore. Resumes the first
     * suspending acquirer if there is one at the point of invocation.
     * Throws [IllegalStateException] if the number of [release] invocations is greater than the number of preceding [acquire].
     *
     * It is recommended to use [withPermit] for safety reasons, so that the acquired permit is always
     * released at the end of your critical section and [release] is never invoked before a successful
     * permit acquisition.
     */
    public fun release()
}

/**
 * Creates new [Semaphore] instance.
 * @param permits the number of permits available in this semaphore.
 * @param acquiredPermits the number of already acquired permits,
 *        should be between `0` and `permits` (inclusively).
 */
@Suppress("FunctionName")
public fun Semaphore(permits: Int, acquiredPermits: Int = 0): Semaphore = SemaphoreImpl(permits, acquiredPermits)

/**
 * Executes the given [action], acquiring a permit from this semaphore at the beginning
 * and releasing it after the [action] is completed.
 *
 * @return the return value of the [action].
 */
@OptIn(ExperimentalContracts::class)
public suspend inline fun <T> Semaphore.withPermit(action: () -> T): T {
    contract {
        callsInPlace(action, InvocationKind.EXACTLY_ONCE)
    }

    acquire()
    try {
        return action()
    } finally {
        release()
    }
}

internal open class SemaphoreImpl(
    private val permits: Int,
    acquiredPermits: Int
) : SegmentQueueSynchronizer<Unit>(), Semaphore {
    init {
        require(permits > 0) { "Semaphore must have at least 1 permit, but is initialized with $permits" }
        require(acquiredPermits in 0..permits) { "The number of acquired permits should be in range [0..$permits]" }
    }

    /**
     * This counter indicates the number of available permits if it is positive,
     * or the negated number of waiters on this semaphore otherwise.
     * Note, that 32-bit counter is enough here since the maximal number of available
     * permits is [permits] which is [Int], and the maximum number of waiting acquirers
     * cannot be greater than 2^31 in any real application.
     */
    private val _availablePermits = atomic(permits - acquiredPermits)
    override val availablePermits: Int get() = max(_availablePermits.value, 0)

    override fun tryAcquire(): Boolean {
        while (true) {
            // Get the current number of available permits.
            val p = _availablePermits.value
            // Is the number of available permits greater
            // than the maximal one because of an incorrect
            // `release()` call without a preceding `acquire()`?
            // Change it to `permits` and start from the beginning.
            if (p > permits) {
                coerceAvailablePermitsAtMaximum()
                continue
            }
            // Try to decrement the number of available
            // permits if it is greater than zero.
            if (p <= 0) return false
            if (_availablePermits.compareAndSet(p, p - 1)) return true
        }
    }

    override suspend fun acquire() {
        while (true) {
            // Decrement the number of available permits.
            val p = decPermits()
            // Is the permit acquired?
            if (p > 0) return
            // Try to suspend otherwise.
            // While it looks better when the following function is inlined,
            // it is important to make `suspend` function invocations in a way
            // so that the tail-call optimization can be applied here.
            return acquireSlowPath()
        }
    }

    private suspend fun acquireSlowPath() = suspendCancellableCoroutineReusable<Unit> sc@{ cont ->
        while (true) {
            // Try to suspend.
            if (suspend(cont)) return@sc
            // The suspension has been failed
            // due to the synchronous resumption mode.
            // Restart the whole `acquire`, and decrement
            // the number of available permits at first.
            val p = decPermits()
            // Is the permit acquired?
            if (p > 0) {
                cont.resume(Unit)
                return@sc
            }
            // Permit has not been acquired, go to
            // the beginning of the loop and suspend.
        }
    }

    /**
     * Decrements the number of available permits
     * and ensures that it is not greater than [permits]
     * at the point of decrement. The last may happen
     * due to an incorrect `release()` call without
     * a preceding `acquire()`.
     */
    private fun decPermits(): Int {
        while (true) {
            // Decrement the number of available permits.
            val p = _availablePermits.getAndDecrement()
            // Is the number of available permits greater
            // than the maximal one due to an incorrect
            // `release()` call without a preceding `acquire()`?
            if (p > permits) continue
            // The number of permits is correct, return it.
            return p
        }
    }

    override fun release() {
        while (true) {
            // Increment the number of available permits.
            val p = _availablePermits.getAndIncrement()
            // Is this `release` call correct and does not
            // exceed the maximal number of permits?
            if (p >= permits) {
                // Revert the number of available permits
                // back to the correct one and fail with error.
                coerceAvailablePermitsAtMaximum()
                error("The number of released permits cannot be greater than $permits")
            }
            // Is there a waiter that should be resumed?
            if (p >= 0) return
            // Try to resume the first waiter, and
            // restart the operation if either this
            // first waiter is cancelled or
            // due to `SYNC` resumption mode.
            if (resume(Unit)) return
        }
    }

    override fun returnValue(value: Unit) {
        // Return the permit if the current continuation
        // is cancelled after the `tryResume` invocation
        // because of the prompt cancellation.
        // Note that this `release()` call can throw
        // exception if there was a successful concurrent
        // `release()` invoked without acquiring a permit.
        release()
    }

    /**
     * Changes the number of available permits to
     * [permits] if it became greater due to an
     * incorrect [release] call.
     */
    private fun coerceAvailablePermitsAtMaximum() {
        while (true) {
            val cur = _availablePermits.value
            if (cur <= permits) break
            if (_availablePermits.compareAndSet(cur, permits)) break
        }
    }
}