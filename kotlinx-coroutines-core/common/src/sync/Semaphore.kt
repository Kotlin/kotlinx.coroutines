/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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
     * *Cancellation of suspended semaphore acquisition is atomic* -- when this function
     * throws [CancellationException] it means that the semaphore was not acquired.
     *
     * Note, that this function does not check for cancellation when it does not suspend.
     * Use [CoroutineScope.isActive] or [CoroutineScope.ensureActive] to periodically
     * check for cancellation in tight loops if needed.
     *
     * Use [tryAcquire] to try acquire a permit of this semaphore without suspension.
     */
    public suspend fun acquire()

    /**
     * Tries to acquire a permit from this semaphore without suspension.
     *
     * @return `true` if a permit was acquired, `false` otherwise.
     */
    public fun tryAcquire(): Boolean

    /**
     * Releases a permit, returning it into this semaphore. Resumes the first
     * suspending acquirer if there is one at the point of invocation.
     * Throws [IllegalStateException] if the number of [release] invocations is greater than the number of preceding [acquire].
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

private class SemaphoreImpl(private val permits: Int, acquiredPermits: Int) : SegmentQueueSynchronizer<Unit>(), Semaphore {
    init {
        require(permits > 0) { "Semaphore should have at least 1 permit, but had $permits" }
        require(acquiredPermits in 0..permits) { "The number of acquired permits should be in 0..$permits" }
    }

    /**
     * This counter indicates a number of available permits if it is non-negative,
     * or the size with minus sign otherwise. Note, that 32-bit counter is enough here
     * since the maximal number of available permits is [permits] which is [Int],
     * and the maximum number of waiting acquirers cannot be greater than 2^31 in any
     * real application.
     */
    private val _availablePermits = atomic(permits - acquiredPermits)
    override val availablePermits: Int get() = max(_availablePermits.value, 0)

    override fun tryAcquire(): Boolean = _availablePermits.loop { p ->
        // Try to decrement the number of available
        // permits if it is greater than zero.
        if (p <= 0) return false
        if (_availablePermits.compareAndSet(p, p - 1)) return true
    }

    override suspend fun acquire() {
        // Decrement the number of available permits.
        val p = _availablePermits.getAndDecrement()
        // Is the permit acquired?
        if (p > 0) return
        // Try to suspend otherwise.
        // While it looks better when the following function is inlined,
        // it is important to make `suspend` function invocations in a way
        // so that the tail-call optimization can be applied.
        acquireSlowPath()
    }

    private suspend fun acquireSlowPath() = suspendAtomicCancellableCoroutineReusable<Unit> sc@ { cont ->
        while (true) {
            // Try to suspend.
            if (suspend(cont)) return@sc
            // The suspension has been failed
            // due to the synchronous resumption mode.
            // Restart the whole acquire, and decrement
            // the number of available permits at first.
            val p = _availablePermits.getAndDecrement()
            // Is the permit acquired?
            if (p > 0) {
                cont.resume(Unit)
                return@sc
            }
            // Otherwise, go to the beginning of
            // the loop and try to suspend otherwise.
        }
    }

    override fun release() {
        while (true) {
            // Increment the number of available permits
            // if it does not exceed the maximum value.
            val p = _availablePermits.getAndUpdate { cur ->
                check(cur < permits) { "The number of released permits cannot be greater than $permits" }
                cur + 1
            }
            // Is there a waiter that should be resumed?
            if (p >= 0) return
            // Try to resume the first waiter, and
            // re-start the operation if it is cancelled.
            if (resume(Unit)) return
        }
    }
}