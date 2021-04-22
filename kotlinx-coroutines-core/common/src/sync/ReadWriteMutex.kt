/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.sync

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.internal.SegmentQueueSynchronizer.CancellationMode.*
import kotlinx.coroutines.internal.SegmentQueueSynchronizer.ResumeMode.*
import kotlinx.coroutines.selects.*
import kotlinx.coroutines.sync.ReadWriteMutexImpl.WriteUnlockPolicy.*
import kotlin.contracts.*
import kotlin.js.*

/**
 * This readers-writer mutex maintains a logical pair of locks, one for read-only
 * operations that can be processed concurrently (see [readLock()][readLock] and [readUnlock()][readUnlock]),
 * and another one for write operations that require an exclusive access (see [write]).
 * It is guaranteed that write and read operations never interfere.
 *
 * The table below shows which locks can be held simultaneously.
 * +-------------+-------------+-------------+
 * |             | reader lock | writer lock |
 * +-------------+-------------+-------------+
 * | reader lock |   ALLOWED   |  FORBIDDEN  |
 * +-------------+-------------+-------------+
 * | writer lock |  FORBIDDEN  |  FORBIDDEN  |
 * +-------------+-------------+-------------+
 *
 * Similar to [Mutex], this readers-writer mutex is **non-reentrant**,
 * so invoking [readLock()][readLock] or [write.lock()][write] even from the coroutine that
 * currently holds the corresponding lock suspends the invoker. Likewise, invoking
 * [readLock()][readLock] from the holder of the writer lock also suspends the invoker.
 *
 * Typical usage of [ReadWriteMutex] is wrapping each read invocation with
 * [read { ... }][read] and each write invocation with [write { ... }][write].
 * These wrapper functions guarantee that the readers-writer mutex is used correctly
 * and safely. However, one can use `lock()` and `unlock()` operations directly.
 *
 * The advantage of using [ReadWriteMutex] compared to the plain [Mutex] is the ability
 * to parallelize read operations and, therefore, increase the level of concurrency.
 * This is extremely useful for the workloads with dominating read operations so they can be
 * executed in parallel, improving the performance and scalability. However, depending on the
 * updates frequency, the execution cost of read and write operations, and the contention,
 * it can be simpler and cheaper to use the plain [Mutex]. Therefore, it is highly recommended
 * to measure the performance difference to make the right choice.
 */
@ExperimentalCoroutinesApi
public interface ReadWriteMutex {
    /**
     * // TODO: how to reference `val write: Mutex` instead of the extension function?
     * Acquires a reader lock of this mutex if the [writer lock][write] is not held and there is no writer
     * waiting for it. Suspends the caller otherwise until the writer lock is released and this reader is resumed.
     * Please note, that in this case the next waiting writer instead of this reader can be resumed after
     * the currently active writer releases the lock.
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
     * It is recommended to use [read { ... }][read] block for safety reasons, so the acquired reader lock
     * is always released at the end of the critical section, and [readUnlock()][readUnlock] is never invoked
     * before a successful [readLock()][readLock].
     */
    @ExperimentalCoroutinesApi
    public suspend fun readLock()

    /**
     * Releases a reader lock of this mutex and resumes the first waiting writer
     * if this operation has released the last acquired reader lock.
     *
     * It is recommended to use [read { ... }][read] block for safety reasons, so the acquired reader lock
     * is always released at the end of the critical section, and [readUnlock()][readUnlock] is never invoked
     * before a successful [readLock()][readLock].
     */
    @ExperimentalCoroutinesApi
    public fun readUnlock()

    /**
     * Returns a [mutex][Mutex] which manipulates with the writer lock of this [ReadWriteMutex].
     *
     * When acquires the writer lock, the operation completes immediately if neither the writer lock nor
     * a reader lock is held. Otherwise, the acquisition suspends the caller until the exclusive access
     * is granted by either [readUnlock()][readUnlock] or [write.unlock()][Mutex.unlock]. Please note that
     * all suspended writers are processed in first-in-first-out (FIFO) order.
     *
     * When releasing the writer lock, the operation resumes the first waiting writer or waiting readers.
     * Note that different fairness policies can be applied by an implementation, such as
     * prioritizing readers or writers and attempting to always resume them at first,
     * choosing the prioritization policy by flipping a coin, or providing a truly fair
     * strategy where all waiters, both readers and writers, form a single FIFO queue.
     *
     * This [Mutex] implementation for writers does not support owners in [lock()][Mutex.lock]
     * and [withLock { ... }][Mutex.withLock] functions as well as the [onLock][Mutex.onLock] select clause.
     *
     * It is also recommended to use [write { ... }][write] block for safety reasons, so the acquired writer lock
     * is always released at the end of the critical section, and [write.unlock()][Mutex.unlock] is never invoked
     * before a successful [write.lock()][Mutex.lock].
     */
    @ExperimentalCoroutinesApi
    public val write: Mutex
}

/**
 * Creates a new [ReadWriteMutex] instance, both reader and writer locks are not acquired.
 *
 * Instead of ensuring the strict fairness, when all waiting readers and writers form
 * a single queue, this implementation provides a slightly relaxed but more efficient guarantee.
 * In this version, two separate queues for waiting readers and waiting writers are maintained.
 * When the last reader lock is released, the first waiting writer is released -- this behaviour
 * respects the strict fairness property. However, when the writer lock is released, the implementation
 * either releases all the waiting readers or the first waiting writer, choosing the policy by the
 * round-robin strategy. Thus, if the choice differs from the strict fairness, it is guaranteed that
 * the proper waiter(s) will be resumed on the next step. Simultaneously, we find it more efficient to
 * resume all waiting readers even if it violates the strict fairness.
 */
@JsName("_ReadWriteMutex")
public fun ReadWriteMutex(): ReadWriteMutex = ReadWriteMutexImpl()

/**
 * Executes the given [action] under a _reader_ lock of this readers-writer mutex.
 *
 * @return the return value of the [action].
 */
@OptIn(ExperimentalContracts::class)
public suspend inline fun <T> ReadWriteMutex.read(action: () -> T): T {
    contract {
        callsInPlace(action, InvocationKind.EXACTLY_ONCE)
    }

    readLock()
    try {
       return action()
    } finally {
        readUnlock()
    }
}

/**
 * Executes the given [action] under the _writer_ lock of this readers-writer mutex.
 *
 * @return the return value of the [action].
 */
public suspend inline fun <T> ReadWriteMutex.write(action: () -> T): T =
    write.withLock(null, action)

/**
 * This readers-writer mutex maintains the numbers of active and waiting readers,
 * a flag on whether the writer lock is acquired, and the number of writers waiting
 * for the lock. This tuple represents the current state of the readers-writer mutex and
 * is split into [waitingReaders] and [state] fields -- it is impossible to store everything
 * in a single register since its maximal capacity is 64 bit, and this is not sufficient
 * for three counters and several flags. Additionally, separate [SegmentQueueSynchronizer]-s
 * are used for waiting readers and writers.
 *
 * To acquire a reader lock, the algorithm checks whether the writer lock is held or there is a writer
 * waiting for it, increasing the number of _active_ readers and grabbing a read lock immediately if not.
 * Otherwise, it atomically decreases the number of _active_ readers and increases the number of _waiting_
 * readers and suspends.
 * As for the writer lock acquisition, the idea is the same -- the algorithm checks whether both reader and
 * writer locks are not acquired and takes the lock immediately in this case. Otherwise, if the writer should
 * wait for the lock, the algorithm increases the counter of waiting writers and suspends.
 *
 * When releasing a reader lock, the algorithm decrements the number of active readers.
 * If the counter reaches zero, it checks whether a writer is waiting for the lock
 * and resumes the first waiting one.
 * On the writer lock release, the algorithm resumes either the next waiting writer
 * (decrementing the counter of them) or all waiting readers (decrementing the counter of waiting
 * readers and incrementing the counter of active ones).
 *
 * When there are both readers and writers waiting for a lock at the point of the writer lock release,
 * the truly fair implementation would form a single queue where all waiters, both readers and writers,
 * are stored. Instead of ensuring the strict fairness, this implementation provides a slightly relaxed
 * but more efficient guarantee. In short, it maintains two separate queues, for waiting readers and
 * waiting writers. When the writer lock is released, the algorithm either releases all the waiting readers
 * or the first waiting writer, choosing the policy by the round-robin strategy. Thus, if the choice differs
 * from the strict fairness, it is guaranteed that the proper waiter(s) will be resumed on the next step.
 * Simultaneously, we find it more efficient to resume all waiting readers even if it violates the strict fairness.
 *
 * As for cancellation, the main idea is to revert the state update. However, possible logical races
 * should be managed carefully, which makes the revert part non-trivial. The details are discussed in the code
 * comments and appear almost everywhere.
 */
internal class ReadWriteMutexImpl : ReadWriteMutex, Mutex {
    // The number of coroutines waiting for a reader lock in `sqsReaders`.
    private val waitingReaders = atomic(0)
    // This state field contains several counters and is always updated atomically by `CAS`:
    // - `AR` (active readers) is a 30-bit counter which represents the number
    //                         of coroutines holding a read lock;
    // - `WLA` (writer lock acquired) is a flag which is `true` when
    //                                the writer lock is acquired;
    // - `WW` (waiting writers) is a 30-bit counter which represents the number
    //                          of coroutines waiting for the writer lock in `sqsWriters`;
    // - `RWR` (resuming waiting readers) is a flag which is `true` when waiting readers
    //                                    resumption is in progress.
    private val state = atomic(0L)

    private val sqsReaders = ReadersSQS() // the place where readers should suspend and be resumed
    private val sqsWriters = WritersSQS() // the place where writers should suspend and be resumed

    private var curUnlockPolicy = false // false -- prioritize readers on the writer lock release
                                        // true  -- prioritize writers on the writer lock release

    @ExperimentalCoroutinesApi
    override val write: Mutex get() = this // we do not create an extra object this way.
    override val isLocked: Boolean get() = state.value.wla
    override fun tryLock(owner: Any?): Boolean = error("ReadWriteMutex.write does not support `tryLock()`")
    override suspend fun lock(owner: Any?) {
        if (owner != null) error("ReadWriteMutex.write does not support owners")
        writeLock()
    }
    override val onLock: SelectClause2<Any?, Mutex> get() = error("ReadWriteMutex.write does not support `onLock`")
    override fun holdsLock(owner: Any) = error("ReadWriteMutex.write does not support owners")
    override fun unlock(owner: Any?) {
        if (owner != null) error("ReadWriteMutex.write does not support owners")
        writeUnlock()
    }

    override suspend fun readLock() {
        // Try to acquire a reader lock without suspension.
        if (tryReadLock()) return
        // The attempt fails, invoke the slow-path. This slow-path
        // part is implemented in a separate function to guarantee
        // that the tail call optimization is applied here.
        readLockSlowPath()
    }

    private fun tryReadLock(): Boolean {
        while (true) {
            // Read the current state.
            val s = state.value
            // Is the writer lock acquired or is there a waiting writer?
            if (!s.wla && s.ww <= 0) {
                // A reader lock is available to acquire, try to do it!
                // Note that there can be a concurrent `write.unlock()` which is
                // resuming readers now, so the `RWR` flag is set in this case.
                if (state.compareAndSet(s, state(s.ar + 1, false, 0, s.rwr)))
                    return true
                // CAS failed => the state has changed.
                // Re-read it and try to acquire a reader lock again.
                continue
            } else return false
        }
    }

    private suspend fun readLockSlowPath() {
        // Increment the number of waiting readers at first.
        // If the current invocation should not suspend,
        // the counter will be decremented back later.
        waitingReaders.incrementAndGet()
        // Check whether this operation should suspend. If not, try
        // to decrement the counter of waiting readers and restart.
        while (true) {
            // Read the current state.
            val s = state.value
            // Is there a writer holding the lock or waiting for it?
            if (s.wla || s.ww > 0) {
                // The number of waiting readers was incremented
                // correctly, wait for a reader lock in `sqsReaders`.
                suspendCancellableCoroutineReusable<Unit> { cont ->
                    sqsReaders.suspend(cont)
                }
                return
            } else {
                // A race has been detected! The increment of the counter of
                // waiting readers was wrong, try to decrement it back. However,
                // it could already become zero due to a concurrent `write.unlock()`
                // which reads the number of waiting readers, replaces it with `0`,
                // and resumes all these readers. In this case, it is guaranteed
                // that a reader lock will be provided via `sqsReaders`.
                while (true) {
                    // Read the current number of waiting readers.
                    val wr = waitingReaders.value
                    // Is our invocation already handled by a concurrent
                    // `write.unlock()` and a reader lock is going to be
                    // passed via `sqsReaders`? Suspend in this case --
                    // it is guaranteed that the lock will be provided
                    // when this concurrent `write.unlock()` completes.
                    if (wr == 0) {
                        suspendCancellableCoroutineReusable<Unit> { cont ->
                            sqsReaders.suspend(cont)
                        }
                        return
                    }
                    // Otherwise, try to decrement the number of waiting
                    // readers and retry the operation from the beginning.
                    if (waitingReaders.compareAndSet(wr, wr - 1)) {
                        // Try again starting from the fast path.
                        readLock()
                        return
                    }
                }
            }
        }
    }

    override fun readUnlock() {
        // When releasing a reader lock, the algorithm checks whether
        // this reader lock is the last acquired one and resumes
        // the first waiting writer (if applicable) in this case.
        while (true) {
            // Read the current state.
            val s = state.value
            check(!s.wla) { "Invalid `readUnlock` invocation: the writer lock is acquired. $INVALID_UNLOCK_INVOCATION_TIP" }
            check(s.ar > 0) { "Invalid `readUnlock` invocation: no reader lock is acquired. $INVALID_UNLOCK_INVOCATION_TIP" }
            // Is this reader the last one and is the `RWR` flag unset (=> it is valid to resume the next writer)?
            if (s.ar == 1 && !s.rwr) {
                // Check whether there is a waiting writer and resume it.
                // Otherwise, simply change the state and finish.
                if (s.ww > 0) {
                    // Try to decrement the number of waiting writers and set the `WLA` flag.
                    // Resume the first waiting writer on success.
                    if (state.compareAndSet(s, state(0, true, s.ww - 1, false))) {
                        sqsWriters.resume(Unit)
                        return
                    }
                } else {
                    // There is no waiting writer according to the state.
                    // Try to clear the number of active readers and finish.
                    if (state.compareAndSet(s, state(0, false, 0, false)))
                        return
                }
            } else {
                // Try to decrement the number of active readers and finish.
                // Please note that the `RWR` flag can be set here if there is
                // a concurrent unfinished `write.unlock()` operation which
                // has resumed the current reader but the corresponding
                // `readUnlock()` happened before this `write.unlock()` completion.
                if (state.compareAndSet(s, state(s.ar - 1, false, s.ww, s.rwr)))
                    return
            }
        }
    }

    /**
     * This customization of [SegmentQueueSynchronizer] for waiting readers
     * use the asynchronous resumption mode and smart cancellation mode,
     * so neither [suspend] nor [resume] fail. However, to support
     * `tryReadLock()` the synchronous resumption mode should be used.
     */
    private inner class ReadersSQS : SegmentQueueSynchronizer<Unit>() {
        override val resumeMode get() = ASYNC
        override val cancellationMode get() = SMART

        override fun onCancellation(): Boolean {
            // The cancellation logic here is pretty similar to
            // the one in `readLock()` when the number of waiting
            // readers has been incremented incorrectly.
            while (true) {
                // First, read the current number of waiting readers.
                val wr = waitingReaders.value
                // Check whether it has already reached zero -- in this
                // case a concurrent `write.unlock()` will invoke `resume()`
                // for this cancelled operation eventually, so `onCancellation()`
                // should return `false` to refuse the granted lock.
                if (wr == 0) return false
                // Otherwise, try to decrement the number of waiting readers keeping
                // the counter non-negative and successfully finish the cancellation.
                if (waitingReaders.compareAndSet(wr, wr - 1)) return true
            }
        }

        // When `onCancellation()` fails, the state keeps unchanged. Therefore,
        // the reader lock should be returned back to the mutex in `returnValue(..)`.
        override fun tryReturnRefusedValue(value: Unit) = false

        // Returns the reader lock back to the mutex.
        // This function is also used for prompt cancellation.
        override fun returnValue(value: Unit) = readUnlock()
    }

    internal suspend fun writeLock() {
        // The algorithm is straightforward -- it reads the current state,
        // checks that there is no reader or writer lock acquired, and
        // tries to change the state by atomically setting the `WLA` flag.
        // Otherwise, if the writer lock cannot be acquired immediatelly,
        // it increments the number of waiting writers and suspends in
        // `sqsWriters` waiting for the lock.
        while (true) {
            // Read the current state.
            val s = state.value
            // Is there an active writer (the WLA flag is set), a concurrent `writeUnlock` operation,
            // which is releasing readers now (the RWR flag is set), or an active reader (AR >= 0)?
            if (!s.wla && !s.rwr && s.ar == 0) {
                // Try to acquire the writer lock, re-try the operation if this CAS fails.
                assert { s.ww == 0 }
                if (state.compareAndSet(s, state(0, true, 0, false)))
                    return
            } else {
                // The lock cannot be acquired immediately, and this operation has to suspend.
                // Try to increment the number of waiting writers and suspend in `sqsWriters`.
                if (state.compareAndSet(s, state(s.ar, s.wla, s.ww + 1, s.rwr))) {
                    suspendCancellableCoroutineReusable<Unit> { cont ->
                        sqsWriters.suspend(cont)
                    }
                    return
                }
            }
        }
    }

    internal fun writeUnlock() {
        // Since we store waiting readers and writers separately, it is not easy
        // to determine whether the next readers or the next writer should be resumed.
        // However, it is natural to have the following policies:
        // - PRIORITIZE_READERS -- always resume all waiting readers at first;
        //   the next waiting writer is resumed only if no reader is waiting for a lock.
        // - PRIORITIZE_WRITERS -- always resumed the next writer first;
        // - ROUND_ROBIN -- switch between the policies above on every invocation.
        //
        // We find the round-robin strategy fair enough in practice, but the others are used
        // in Lincheck tests. However, it could be useful to have `PRIORITIZE_WRITERS` policy
        // in the public API for the cases when the writer lock is used for UI updates.
        writeUnlock(ROUND_ROBIN)
    }

    internal fun writeUnlock(policy: WriteUnlockPolicy) {
        // The algorithm for releasing the writer lock is straightforward by design,
        // but has a lot of corner cases that should be properly managed.
        // If the next writer should be resumed (see `PRIORITIZE_WRITERS` policy),
        // the algorithm tries to atomically decrement the number of waiting writers
        // and keep the `WLA` flag, resuming the first writer in `sqsWriters` after that.
        // Otherwise, if the `PRIORITIZE_READERS` policy is used or there is no waiting writer,
        // the algorithm sets the `RWR` (resuming waiting readers) flag and invokes a special
        // `completeWaitingReadersResumption()` to resume all the waiting readers.
        while (true) {
            // Read the current state at first.
            val s = state.value
            check(s.wla) { "Invalid `writeUnlock` invocation: the writer lock is not acquired. $INVALID_UNLOCK_INVOCATION_TIP" }
            assertNot { s.rwr }
            assert { s.ar == 0 }
            // Should we resume the next writer?
            curUnlockPolicy = !curUnlockPolicy // change the unlock policy for the `ROUND_ROBIN` strategy
            val resumeWriter = (s.ww > 0) && (policy == PRIORITIZE_WRITERS || policy == ROUND_ROBIN && curUnlockPolicy)
            if (resumeWriter) {
                // Resume the next writer - try to decrement the number of waiting
                // writers and resume the first one in `sqsWriters` on success.
                if (state.compareAndSet(s, state(0, true, s.ww - 1, false))) {
                    sqsWriters.resume(Unit)
                    return
                }
            } else {
                // Resume waiting readers. Reset the `WLA` flag and set the `RWR` flag atomically,
                // completing the resumption via `completeWaitingReadersResumption()` after that.
                // Note that this function also checks whether the next waiting writer should be resumed
                // on completion and does it if required. It also resets the `RWR` flag at the end.
                // While it is possible that no reader is waiting for a lock, so that this CAS can be omitted,
                // we do not add the corresponding code for simplicity since it does not improve the performance
                // significantly but reduces the code readability.
                if (state.compareAndSet(s, state(0, false, s.ww, true))) {
                    completeWaitingReadersResumption()
                    return
                }
            }
        }
    }

    private fun completeWaitingReadersResumption() {
        // This function is called after the `RWR` flag is set
        // and completes the readers resumption process. Note that
        // it also checks whether the next waiting writer should be
        // resumed on completion and performs this resumption if needed.
        assert { state.value.rwr }
        // At first, atomically replace the number of waiting
        // readers (to be resumed) with 0, retrieving the old value.
        val wr = waitingReaders.getAndSet(0)
        // After that, these waiting readers should be logically resumed
        // by incrementing the corresponding counter in the `state` field.
        // We also skip this step if the obtained number of waiting readers is zero.
        if (wr > 0) { // should we update the state?
            state.update { s ->
                assertNot { s.wla } // the writer lock cannot be acquired now.
                assert { s.rwr } // the `RWR` flag should still be set.
                state(s.ar + wr, false, s.ww, true)
            }
        }
        // After the readers are resumed logically, they should be resumed physically in `sqsReaders`.
        repeat(wr) {
            sqsReaders.resume(Unit)
        }
        // Once all the waiting readers are resumed, the `RWR` flag should be reset.
        // It is possible that all the resumed readers have already completed their
        // work and successfully invoked `readUnlock()` at this point, but since
        // the `RWR` flag was set, they were unable to resume the next waiting writer.
        // Similarly, it is possible that there were no waiting readers at all.
        // Therefore, in the end, we check whether the number of active readers is 0
        // and resume the next waiting writer in this case (if there exists one).
        var resumeWriter = false
        state.getAndUpdate { s ->
            resumeWriter = s.ar == 0 && s.ww > 0
            val wwUpd = if (resumeWriter) s.ww - 1 else s.ww
            state(s.ar, resumeWriter, wwUpd, false)
        }
        if (resumeWriter) {
            // Resume the next writer physically and finish
            sqsWriters.resume(Unit)
            return
        }
        // Meanwhile, it could be possible for a writer to come and suspend due to the `RWR` flag.
        // After that, all the following readers suspend since a writer is waiting for the lock.
        // However, if the writer becomes canceled, it cannot resume these suspended readers if the `RWR` flag
        // is still set, so we have to help him with the resumption process. To detect such a situation, we re-read
        // the number of waiting readers and try to start the resumption process again if the writer lock is not acquired.
        if (waitingReaders.value > 0) { // Is there a waiting reader?
            while (true) {
                val s = state.value // Read the current state.
                if (s.wla || s.ww > 0 || s.rwr) return // Check whether the readers resumption is valid.
                // Try to set the `RWR` flag again and resume the waiting readers.
                if (state.compareAndSet(s, state(s.ar, false, 0, true))) {
                    completeWaitingReadersResumption()
                    return
                }
            }
        }
    }

    /**
     * This customization of [SegmentQueueSynchronizer] for waiting writers
     * uses the asynchronous resumption mode and smart cancellation mode,
     * so neither [suspend] nor [resume] fail. However, in order to support
     * `tryWriteLock()` the synchronous resumption mode should be used instead.
     */
    private inner class WritersSQS : SegmentQueueSynchronizer<Unit>() {
        override val resumeMode get() = ASYNC
        override val cancellationMode get() = SMART

        override fun onCancellation(): Boolean {
            // In general, on cancellation, the algorithm tries to decrement the number of waiting writers.
            // Similarly to the cancellation logic for readers, if the number of waiting writers has already reached 0,
            // the current canceling writer will be resumed in `sqsWriters`. In this case, the function returns
            // `false`, and the permit will be returned via `returnValue()`. Otherwise, if the number of waiting
            // writers >= 1, the decrement is sufficient. However, if this canceling writer is the last waiting one,
            // the algorithm sets the `RWR` flag and resumes waiting readers. This logic is similar to `writeUnlock(..)`.
            while (true) {
                val s = state.value // Read the current state.
                if (s.ww == 0) return false // Is this writer going to be resumed in `sqsWriters`?
                // Is this writer the last one and is the readers resumption valid?
                if (s.ww == 1 && !s.wla && !s.rwr) {
                    // Set the `RWR` flag and resume the waiting readers.
                    // While it is possible that no reader is waiting for a lock, so that this CAS can be omitted,
                    // we do not add the corresponding code for simplicity since it does not improve the performance
                    // significantly but reduces the code readability. Note that the same logic appears in `writeUnlock(..)`,
                    // and the cancellation performance is less critical since the cancellation itself does not come for free.
                    if (state.compareAndSet(s, state(s.ar, false, 0, true))) {
                        completeWaitingReadersResumption()
                        return true
                    }
                } else {
                    // There are multiple writers waiting for the lock. Try to decrement the number of them.
                    if (state.compareAndSet(s, state(s.ar, s.wla, s.ww - 1, s.rwr)))
                        return true
                }
            }
        }

        // Resumes the next waiting writer if the current `writeLock()` operation
        // is already cancelled but the next writer is logically resumed
        override fun tryReturnRefusedValue(value: Unit): Boolean {
            writeUnlock(PRIORITIZE_WRITERS)
            return true
        }

        // Returns the writer lock back to the mutex.
        // This function is also used for prompt cancellation.
        override fun returnValue(value: Unit) = writeUnlock()
    }

    // This state representation is used in Lincheck tests.
    internal val stateRepresentation: String get() =
        "<wr=${waitingReaders.value},ar=${state.value.ar}" +
        ",wla=${state.value.wla},ww=${state.value.ww}" +
        ",rwr=${state.value.rwr}" +
        ",sqs_r={$sqsReaders},sqs_w={$sqsWriters}>"

    internal enum class WriteUnlockPolicy { PRIORITIZE_READERS, PRIORITIZE_WRITERS, ROUND_ROBIN }
}

/**
 * Constructs a value for [ReadWriteMutexImpl.state] field.
 * The created state can be parsed via the extension functions below.
 */
private fun state(activeReaders: Int, writeLockAcquired: Boolean, waitingWriters: Int, resumingWaitingReaders: Boolean): Long =
    (if (writeLockAcquired) WLA_BIT else 0) +
    (if (resumingWaitingReaders) RWR_BIT else 0) +
    activeReaders * AR_MULTIPLIER +
    waitingWriters * WW_MULTIPLIER

// Equals `true` if the `WLA` flag is set in this state.
private val Long.wla: Boolean get() = this or WLA_BIT == this
// Equals `true` if the `RWR` flag is set in this state.
private val Long.rwr: Boolean get() = this or RWR_BIT == this
// The number of waiting writers specified in this state.
private val Long.ww: Int get() = ((this % AR_MULTIPLIER) / WW_MULTIPLIER).toInt()
// The number of active readers specified in this state.
private val Long.ar: Int get() = (this / AR_MULTIPLIER).toInt()

private const val WLA_BIT = 1L
private const val RWR_BIT = 1L shl 1
private const val WW_MULTIPLIER = 1L shl 2
private const val AR_MULTIPLIER = 1L shl 33

private const val INVALID_UNLOCK_INVOCATION_TIP = "This can be caused by releasing the lock without acquiring it at first, " +
    "or incorrectly putting the acquisition inside the \"try\" block of the \"try-finally\" section that safely releases " +
    "the lock in the \"finally\" block - the acquisition should be performed right before this \"try\" block."