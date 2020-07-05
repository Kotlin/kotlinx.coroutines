/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.SegmentQueueSynchronizerJVM.ResumeMode.ASYNC
import kotlinx.coroutines.SegmentQueueSynchronizerJVM.ResumeMode.SYNC
import kotlinx.coroutines.SegmentQueueSynchronizerJVM.CancellationMode.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.sync.*
import java.util.concurrent.*
import java.util.concurrent.locks.*
import kotlin.coroutines.*

/**
 * [SegmentQueueSynchronizerJVM] is an abstraction for implementing _fair_ synchronization
 * and communication primitives. It maintains a FIFO queue of waiting requests and is
 * provided with two main functions:
 * + [suspend] that stores the specified waiter into the queue, and
 * + [resume] that tries to retrieve and resume the first waiter with the specified value.
 *
 * One may consider this abstraction as an infinite array with two counters that reference the next cells
 * for enqueueing a continuation in [suspend] and for retrieving it in [resume]. To be short, when
 * [suspend] is invoked, it increments the corresponding counter via fast `Fetch-And-Add` and stores the
 * continuation into the cell. At the same time, [resume] increments its own counter and comes to the
 * corresponding cell.
 *
 * A typical implementation via [SegmentQueueSynchronizerJVM] performs some synchronization at first,
 * (e.g., [Semaphore] modifies the number of available permits), and invokes [suspend] or [resume]
 * after that. Following this pattern, it is possible in a concurrent environment that [resume]
 * is executed before [suspend] (similarly to the race between `park` and `unpark` for threads),
 * so that [resume] comes to a cell in the empty state. This race can be solved with two [strategies][ResumeMode]:
 * [asynchronous][ASYNC] and [synchronous][SYNC]. In the [asynchronous][ASYNC] mode, [resume] puts
 * the value into the cell if it is still empty and finishes immediately; this way, the following [suspend] comes
 * to this cell and simply grabs the element without suspension. At the same time, in the [synchronous][SYNC] mode,
 * [resume] waits in a bounded spin-loop cycle until the put element is taken by a concurrent [suspend],
 * marking the cell as broken if it is not taken after the spin-loop is finished. In this case, both the current
 * [resume] and the [suspend] that comes to this broken cell fail and the corresponding operations on the data
 * structure are typically restarted from the beginning.
 *
 * Since [suspend] can store [CancellableContinuation]-s, it is possible for [resume] to fail if the
 * continuation is already cancelled. In this case, most of the algorithms retry the whole operation.
 * However, if there are many consecutive cancelled waiters, it seems more efficient to skip them
 * somehow. Thus, there are different [cancellation modes][cancellationMode] that can be used.
 * In the simple mode ([SIMPLE]), which is used by default, [resume] simply fails on cancelled waiters as
 * described above, while in smart modes ([SMART_SYNC] and [SMART_ASYNC]) [resume] skips cells in the
 * [cancelled][CANCELLED] state. However, if cancellation happens concurrently with [resume], it can be illegal
 * to simply skip the cell and resume the next waiter, e.g., if this cancelled waiter is the last one.
 * Thus, it is possible for [SegmentQueueSynchronizerJVM] to refuse this [resume]. In order to support this logic,
 * users should implement  [onCancellation] function, which returns `true` if the cell can be
 * moved to the [cancelled][CANCELLED] state, or `false` if the [resume] that comes to this cell
 * should be refused. In the last case, [tryReturnRefusedValue] is invoked, so that the value
 * can be put back to the data structure. However, it is possible for [tryReturnRefusedValue] to
 * fail, and [returnValue] is called in this case. Typically, this [returnValue] function coincide
 * with the one that resumes waiters (e.g., [release][Semaphore.release] in [Semaphore]). The difference
 * between [SMART_SYNC] and [SMART_ASYNC] modes is that in the first one the [resume] that comes to the
 * cell with cancelled waiter waits in a spin-loop until the cell is marked either with [CANCELLED]
 * or [REFUSE] mark, while in [SMART_ASYNC] mode it replaces the cancelled waiter with the value of
 * the resumption and finishes, so that the cancellation handler completes this [resume] eventually.
 * This way, in [SMART_ASYNC] mode the value passed to [resume] can be out of the data structure for a while.
 *
 * Here is a state machine for cells. Note that only one [suspend]
 * and at most one [resume] operation can deal with each cell.
 *
 *  +-------+   `suspend` succeeds.   +--------------+  `resume` is   +---------------+  store `RESUMED` to   +---------+  ( `cont` HAS BEEN   )
 *  |  NULL | ----------------------> | cont: active | -------------> | cont: resumed | --------------------> | RESUMED |  ( RESUMED AND THIS  )
 *  +-------+                         +--------------+  successful.   +---------------+  avoid memory leaks.  +---------+  ( `resume` SUCCEEDS )
 *     |                                     |
 *     |                                     | The continuation
 *     | `resume` comes to                   | is cancelled.
 *     | the cell before                     |
 *     | `suspend` and puts                  V                                                                      ( THE CORRESPONDING `resume` SHOULD BE   )
 *     | the element into           +-----------------+    The concurrent `resume` should be refused,    +--------+ ( REFUSED AND `tryReturnRefusedValue` OR )
 *     | the cell, waiting          | cont: cancelled | -----------------------------------------------> | REFUSE | ( `returnValue` IF IT FAILS IS USED TO   )
 *     | for `suspend` in           +-----------------+      `onCancellation` has returned `false`.      +--------+ ( RETURN THE VALUE BACK TO THE ORIGINAL  )
 *     | SYNC mode.                          |         \                                                     ^      ( SYNCHRONIZATION PRIMITIVE              )
 *     |                                     |          \                                                    |
 *     |        Mark the cell as `CANCELLED` |           \                                                   |
 *     |         if the cancellation mode is |            \  `resume` delegates its completing to            | `onCancellation` returned `false,
 *     |        `SIMPLE` or `onCancellation` |             \   the concurrent cancellation handler if        | mark the state accordingly and
 *     |                has returned `true`. |              \   `SMART_ASYNC` cancellation mode is used.     | complete the hung `resume`.
 *     |                                     |               +------------------------------------------+    |
 *     |                                     |                                                           \   |
 *     |    ( THE CONTINUATION IS    )       V                                                            V  |
 *     |    ( CANCELLED AND `resume` ) +-----------+                                                     +-------+
 *     |    ( EITHER FAILS IN THE    ) | CANCELLED | <-------------------------------------------------- | value |
 *     |    ( SIMPLE CANCELLATION    ) +-----------+   Mark the cell as `CANCELLED` if `onCancellation`  +-------+
 *     |    ( MODE OR SKIPS THIS     )              returned true, complete the hung `resume` accordingly.
 *     |    ( CELL IN THE SMART ONE  )
 *     |
 *     |
 *     |            `suspend` gets   +-------+  ( ELIMINATION HAPPENED, )
 *     |         +-----------------> | TAKEN |  (  BOTH `resume` and    )
 *     V         |   the element.    +-------+  (  `suspend` SUCCEED    )
 *  +-------+    |
 *  | value | --<
 *  +-------+   |
 *              | `tryResume` has waited a bounded time,  +--------+
 *              +---------------------------------------> | BROKEN | (BOTH `suspend` AND `resume` FAIL)
 *                     but `suspend` has not come.        +--------+
 *
 *  As for the infinite array implementation, it is organized as a linked list of [segments][SQSSegment];
 *  each segment contains a fixed number of cells. To determine the cell for each [suspend] and [resume]
 *  invocation, the algorithm reads the current [tail] or [head], increments [enqIdx] or [deqIdx], and
 *  finds the required segment starting from the initially read one.
 */
@InternalCoroutinesApi
public abstract class SegmentQueueSynchronizerJVM<T : Any> {
    private val head: AtomicRef<SQSSegment>
    private val deqIdx = atomic(0L)
    private val tail: AtomicRef<SQSSegment>
    private val enqIdx = atomic(0L)

    init {
        val s = SQSSegment(0, null, 2)
        head = atomic(s)
        tail = atomic(s)
    }

    /**
     * Specifies whether [resume] should work in
     * [synchronous][SYNC] or [asynchronous][ASYNC] mode.
     */
    protected open val resumeMode: ResumeMode get() = SYNC

    /**
     * Specifies whether [resume] should fail on cancelled waiters ([SIMPLE]),
     * or skip them in either [synchronous][SMART_SYNC] or [asynchronous][SMART_ASYNC]
     * way. In the asynchronous mode [resume] may pass the element to the
     * cancellation handler in order not to wait, so that the element can be "hung"
     * for a while, but it is guaranteed that this [resume] will be completed eventually.
     */
    protected open val cancellationMode: CancellationMode get() = SIMPLE

    /**
     * This function is invoked when waiter is cancelled and smart
     * cancellation mode is used (so that cancelled cells are skipped by
     * [resume]). Typically, this function performs the logical cancellation.
     * It returns `true` if the cancellation succeeds and the cell can be
     * marked as [CANCELLED]. This way, a concurrent [resume] skips this cell,
     * and the value stays in the waiting queue. However, if the concurrent
     * [resume] should be refused by this [SegmentQueueSynchronizerJVM],
     * [onCancellation] should return false. In this case, [tryReturnRefusedValue]
     * is invoked with the value of [resume], following by [returnValue]
     * if the attempt fails.
     */
    protected open fun onCancellation() : Boolean = false

    /**
     * This function specifies how the refused by
     * this [SegmentQueueSynchronizerJVM] value should
     * be returned back to the data structure. It
     * returns `true` if succeeds or `false` if the
     * attempt failed, so that [returnValue] should
     * be used to complete the returning.
     */
    protected open fun tryReturnRefusedValue(value: T): Boolean = true

    /**
     * This function specifies how the value from
     * a failed [resume] should be returned back to
     * the data structure. It is typically the function
     * that invokes [resume] (e.g., [release][Semaphore.release]
     * in [Semaphore]).
     */
    protected open fun returnValue(value: T) {}

    /**
     * This is a short-cut for [tryReturnRefusedValue] and
     * the following [returnValue] invocation if it fails.
     */
    private fun returnRefusedValue(value: T) {
        if (tryReturnRefusedValue(value)) return
        returnValue(value)
    }

    /**
     * Puts the specified continuation into the waiting queue, and returns `true` on success.
     * Since [suspend] and [resume] can be invoked concurrently (similarly to `park` and `unpark`
     * for threads), it is possible that [resume] comes earlier. In this case, the [resume] comes
     * to the first cell and puts it value into it. After that, this [suspend] should come and
     * grab the value. However, if the [synchronous][SYNC] resumption mode is used, the concurrent
     * [resume] can mark its cell as [broken][BROKEN]; thus, this [suspend] invocation comes to the
     * broken cell and fails. The typical patter is retrying both operations, the one that
     * failed on [suspend] and the one that failed on [resume], from the beginning.
     */
    @Suppress("UNCHECKED_CAST")
    protected fun suspend(cont: Continuation<T>): Boolean {
        // Increment `enqIdx` and find the segment
        // with the corresponding id. It is guaranteed
        // that this segment is not removed since at
        // least the cell for this [suspend] invocation
        // is not in the `CANCELLED` state.
        val curTail = this.tail.value
        val enqIdx = enqIdx.getAndIncrement()
        val segment = this.tail.findSegmentAndMoveForward(id = enqIdx / SEGMENT_SIZE, startFrom = curTail,
            createNewSegment = ::createSegment).segment
        assert { segment.id == enqIdx / SEGMENT_SIZE }
        // Try to install the continuation in the cell,
        // this is the regular path.
        val i = (enqIdx % SEGMENT_SIZE).toInt()
        // Optimization: spin for a while
        repeat(500) {
            val value = segment.get(i)
            if (value != null) {
                if (value !== BROKEN && segment.cas(i, value, TAKEN)) {
                    // The elimination is successfully performed,
                    // resume the continuation with the value and complete.
                    cont.resume(value as T)
                    return true
                }
                // The cell is broken, this can happen only in `SYNC` resumption mode.
                return false
            }
        }
        if (segment.cas(i, null, cont)) {
            // The continuation is successfully installed,
            // add a cancellation handler if it is cancellable
            // and complete successfully.
            if (cont is CancellableContinuation<*>) {
                cont.invokeOnCancellation(SQSCancellationHandler(segment, i).asHandler)
            }
            return true
        }
        // The continuation installation failed. This can happen only
        // if a concurrent `resume` comes earlier to this cell and put
        // its value into it. Note, that in `SYNC` resumption mode
        // this concurrent `resume` can mark the cell as broken.
        //
        // Try to grab the value if the cell is not in the `BROKEN` state.
        val value = segment.get(i)
        if (value !== BROKEN && segment.cas(i, value, TAKEN)) {
            // The elimination is successfully performed,
            // resume the continuation with the value and complete.
            cont.resume(value as T)
            return true
        }
        // The cell is broken, this can happen only in `SYNC` resumption mode.
        assert { resumeMode == SYNC && segment.get(i) === BROKEN }
        return false
    }

    // false -> failed
    // true -> success
    protected fun suspendCurThread(): T? {
        val t = Thread.currentThread()
        // Increment `enqIdx` and find the segment
        // with the corresponding id. It is guaranteed
        // that this segment is not removed since at
        // least the cell for this [suspend] invocation
        // is not in the `CANCELLED` state.
        val curTail = this.tail.value
        val enqIdx = enqIdx.getAndIncrement()
        val segment = this.tail.findSegmentAndMoveForward(id = enqIdx / SEGMENT_SIZE, startFrom = curTail,
            createNewSegment = ::createSegment).segment
        assert { segment.id == enqIdx / SEGMENT_SIZE }
        // Try to install the continuation in the cell,
        // this is the regular path.
        val i = (enqIdx % SEGMENT_SIZE).toInt()
        // Spin-loop optimization here
        var x = 1
        while (x < 100) {
            val value = segment.get(i)
            if (value != null) {
                if (value !== BROKEN && segment.cas(i, value, TAKEN)) {
                    // The elimination is successfully performed,
                    // resume the continuation with the value and complete.
                    return value as T
                }
                // The cell is broken, this can happen only in `SYNC` resumption mode.
                return null
            }
            doGeomDistrWork(x*x)
            x++
        }
        if (segment.cas(i, null, t)) {
            do {
                LockSupport.park()
            } while (segment.get(i) === t)
            val value = segment.get(i) as T
            segment.set(i, RESUMED)
            return value
        }
        // The continuation installation failed. This can happen only
        // if a concurrent `resume` comes earlier to this cell and put
        // its value into it. Note, that in `SYNC` resumption mode
        // this concurrent `resume` can mark the cell as broken.
        //
        // Try to grab the value if the cell is not in the `BROKEN` state.
        val value = segment.get(i)
        if (value !== BROKEN && segment.cas(i, value, TAKEN)) {
            // The elimination is successfully performed,
            // resume the continuation with the value and complete.
            return value as T
        }
        // The cell is broken, this can happen only in `SYNC` resumption mode.
        return null
    }

    public fun doGeomDistrWork(work: Int) {
        // We use geometric distribution here. We also checked on macbook pro 13" (2017) that the resulting work times
        // are distributed geometrically, see https://github.com/Kotlin/kotlinx.coroutines/pull/1464#discussion_r355705325
        val p = 1.0 / work
        val r = ThreadLocalRandom.current()
        while (true) {
            if (r.nextDouble() < p) break
        }
    }

    /**
     * Tries to resume the next waiter and returns `true` if
     * the resumption succeeds. However, it can fail due to
     * several reasons. First of all, if the [resumption mode][resumeMode]
     * is [synchronous][SYNC], this [resume] invocation may come
     * before [suspend] and mark the cell as [broken][BROKEN];
     * `false` is returned in this case. At the same time, according
     * to the [simple cancellation mode][SIMPLE], this [resume] fails
     * if the next waiter is cancelled, and returns `false` in this case.
     *
     * Note that when smart cancellation ([SMART_SYNC] or [SMART_ASYNC])
     * is used, [resume] skips cancelled waiters and can fail only in
     * case of unsuccessful elimination due to [synchronous][SYNC]
     * resumption mode.
     */
    protected fun resume(value: T): Boolean {
        // Should we skip cancelled cells?
        val skipCancelled = cancellationMode != SIMPLE
        while (true) {
            // Try to resume the next waiter, adjust [deqIdx] if
            // cancelled cells should be skipped anyway.
            when (tryResumeImpl(value, adjustDeqIdx = skipCancelled)) {
                TRY_RESUME_SUCCESS -> return true
                TRY_RESUME_FAIL_CANCELLED -> if (!skipCancelled) return false
                TRY_RESUME_FAIL_BROKEN -> return false
            }
        }
    }

    /**
     * Tries to resume the next waiter, and returns [TRY_RESUME_SUCCESS] on
     * success, [TRY_RESUME_FAIL_CANCELLED] if the next waiter is cancelled,
     * or [TRY_RESUME_FAIL_BROKEN] if the next cell is marked as broken by
     * this [tryResumeImpl] invocation due to the [SYNC] resumption mode.
     *
     * In the smart cancellation modes ([SMART_SYNC] and [SMART_ASYNC]) the
     * cells marked as [cancelled][CANCELLED] should be skipped, so that
     * there is no need to increment [deqIdx] one-by-one is there is a
     * removed segment (logically full of [cancelled][CANCELLED] cells);
     * it is faster to point [deqIdx] to the first possibly non-cancelled
     * cell instead, i.e. to the first segment id multiplied by the
     * [segment size][SEGMENT_SIZE].
     */
    @Suppress("UNCHECKED_CAST")
    private fun tryResumeImpl(value: T, adjustDeqIdx: Boolean): Int {
        // Check that `adjustDeqIdx` is `false`
        // in the simple cancellation mode.
        assert { !(cancellationMode == SIMPLE && adjustDeqIdx) }
        // Increment `deqIdx` and find the first segment with
        // the corresponding or higher (if the required segment
        // is physically removed) id.
        val curHead = this.head.value
        val deqIdx = deqIdx.getAndIncrement()
        val id = deqIdx / SEGMENT_SIZE
        val segment = this.head.findSegmentAndMoveForward(id, startFrom = curHead,
            createNewSegment = ::createSegment).segment
        // The previous segments can be safely collected
        // by GC, clean the pointer to them.
        segment.cleanPrev()
        // Is the required segment physically removed?
        if (segment.id > id) {
            // Adjust `deqIdx` to the first
            // non-removed segment if needed.
            if (adjustDeqIdx) adjustDeqIdx(segment.id * SEGMENT_SIZE)
            // The cell #deqIdx is in the cancelled state,
            // return the corresponding failure.
            return TRY_RESUME_FAIL_CANCELLED
        }
        // Modify the cell according to the state machine,
        // all the transitions are performed atomically.
        val i = (deqIdx % SEGMENT_SIZE).toInt()
        modify_cell@while (true) {
            val cellState = segment.get(i)
            when {
                // Is the cell empty?
                cellState === null -> {
                    // Try to perform an elimination by putting the
                    // value to the empty cell and wait until it is
                    // taken by a concurrent `suspend` in case of
                    // using the synchronous resumption mode.
                    if (!segment.cas(i, null, value)) continue@modify_cell
                    // Finish immediately in the async mode.
                    if (resumeMode == ASYNC) return TRY_RESUME_SUCCESS
                    // Wait for a concurrent `suspend` for a bounded
                    // time; it should mark the cell as taken.
                    repeat(MAX_SPIN_CYCLES) {
                        if (segment.get(i) === TAKEN) return TRY_RESUME_SUCCESS
                    }
                    // The value is still not taken, try to
                    // atomically mark the cell as broken.
                    // A failure indicates that the value is taken.
                    return if (segment.cas(i, value, BROKEN)) TRY_RESUME_FAIL_BROKEN else TRY_RESUME_SUCCESS
                }
                // Is the waiter cancelled?
                cellState === CANCELLED -> {
                    // Return the corresponding failure.
                    return TRY_RESUME_FAIL_CANCELLED
                }
                // Should the current `resume` be refused
                // by this `SegmentQueueSynchronizer`?
                cellState === REFUSE -> {
                    // This state should not occur
                    // in the simple cancellation mode.
                    assert { cancellationMode != SIMPLE }
                    // Return the refused value back to
                    // the data structure and succeed.
                    returnRefusedValue(value)
                    return TRY_RESUME_SUCCESS
                }
                cellState is Thread -> {
                    segment.set(i, value)
                    LockSupport.unpark(cellState)
                    return TRY_RESUME_SUCCESS
                }
                // Does the cell store a cancellable continuation?
                cellState is CancellableContinuation<*> -> {
                    // Try to resume the continuation.
                    val success = (cellState as CancellableContinuation<T>).tryResume0(value)
                    // Is the resumption successful?
                    if (success) {
                        // Mark the cell as `DONE` to avoid
                        // memory leaks and complete successfully.
                        segment.set(i, RESUMED)
                        return TRY_RESUME_SUCCESS
                    }
                    // The continuation is cancelled, the handling
                    // logic depends on the cancellation mode.
                    when (cancellationMode) {
                        // Fail correspondingly in the simple mode.
                        SIMPLE -> return TRY_RESUME_FAIL_CANCELLED
                        // In the smart cancellation mode this cell
                        // can be either skipped (if it is going to
                        // be marked as cancelled) or this `resume`
                        // should be refused. The `SMART_SYNC` mode
                        // waits in a an infinite spin-loop until
                        // the state of this cell is changed to
                        // either `CANCELLED` or `REFUSE`.
                        SMART_SYNC -> continue@modify_cell
                        // At the same time, in `SMART_ASYNC` mode
                        // `resume` replaces the cancelled continuation
                        // with the resumption value and completes.
                        // Thus, the concurrent cancellation handler
                        // notices this value and completes this `resume`.
                        SMART_ASYNC -> {
                            // Try to put the value into the cell if there is
                            // no decision on whether the cell is in the `CANCELLED`
                            // or `REFUSE` state, and finish if the put is performed.
                            val valueToStore: Any? = if (value is Continuation<*>) WrappedContinuationValue(value) else value
                            if (segment.cas(i, cellState, valueToStore)) return TRY_RESUME_SUCCESS
                        }
                    }
                }
                // The cell stores a non-cancellable
                // continuation, we can simply resume it.
                else -> {
                    // Resume the continuation and mark the cell
                    // as `DONE` to avoid memory leaks.
                    (cellState as Continuation<T>).resume(value)
                    segment.set(i, RESUMED)
                    return TRY_RESUME_SUCCESS
                }
            }
        }
    }

    /**
     * Updates [deqIdx] to [newValue] if the current value is lower.
     * Thus, it is guaranteed that either the update is successfully
     * performed or the value of [deqIdx] is greater or equal to [newValue].
     */
    private fun adjustDeqIdx(newValue: Long): Unit = deqIdx.loop { cur ->
        if (cur >= newValue) return
        if (deqIdx.compareAndSet(cur, newValue)) return
    }

    /**
     * These modes define the strategy that [resume] should
     * use if it comes to the cell before [suspend] and finds it empty.
     * In the [asynchronous][ASYNC] mode, it puts the value into the cell,
     * so that [suspend] grabs it and immediately resumes without actual
     * suspension; in other words, an elimination happens in this case.
     * However, this strategy produces an incorrect behavior when used for some
     * data structures (e.g., for [tryAcquire][Semaphore.tryAcquire] in [Semaphore]),
     * so that the [synchronous][SYNC] is introduced. Similarly to the asynchronous one,
     * [resume] puts the value into the cell, but do not finish right after that.
     * In opposite, it waits in a bounded spin-loop (see [MAX_SPIN_CYCLES]) until
     * the value is taken, completes after that. If the value is not taken after
     * this spin-loop is finished, [resume] marks the cell as [broken][BROKEN]
     * and fails, so that the corresponding [suspend] invocation finds the cell
     * [broken][BROKEN] and fails as well.
     */
    public enum class ResumeMode { SYNC, ASYNC }

    /**
     * These modes define the mode that should be used for cancellation.
     * Essentially, there are two modes: simple and smart.
     * Specifies whether [resume] should fail on cancelled waiters ([SIMPLE]),
     * or skip them in either [synchronous][SMART_SYNC] or [asynchronous][SMART_ASYNC]
     * way. In the asynchronous skip mode [resume] may pass the element to the
     * cancellation handler in order not to wait, so that the element can be "hung"
     * for a while.
     */
    public enum class CancellationMode { SIMPLE, SMART_SYNC, SMART_ASYNC }

    /**
     * This cancellation handler is invoked when
     * the waiter located by ```segment[index]```
     * is cancelled.
     */
    private inner class SQSCancellationHandler(
        private val segment: SQSSegment,
        private val index: Int
    ) : CancelHandler() {
        override fun invoke(cause: Throwable?) {
            // Do we use simple or smart cancellation?
            if (cancellationMode === SIMPLE) {
                // In the simple cancellation mode the logic
                // is straightforward -- mark the  cell as
                // cancelled to avoid memory leaks and complete.
                segment.markCancelled(index)
                return
            }
            // We are in the smart cancellation mode.
            // Perform the cancellation-related logic and
            // check whether the value of the `resume` that
            // comes to this cell should be processed in the
            // `SegmentQueueSynchronizer` or refused by it.
            val cancelled = onCancellation()
            if (cancelled) {
                // The cell should be considered as cancelled.
                // Mark the cell correspondingly and help a
                // concurrent `resume` to process its value if
                // needed (see `SMART_ASYNC` cancellation mode).
                val value = segment.markCancelled(index) ?: return
                // Try to resume the next waiter with the value
                // provided by a concurrent `resume`.
                if (resume(value as T)) return
                // The resumption has been failed because of the
                // `SYNC` resume mode. Return the value back to
                // the original data structure.
                returnValue(value)
            } else {
                // The value of the `resume` that comes to this
                // cell should be refused by this `SegmentQueueSynchronizer`.
                // Mark the cell correspondingly and help a concurrent
                // `resume` to process its value if needed
                // (see `SMART_ASYNC` cancellation mode).
                val value = segment.markRefused(index) ?: return
                returnRefusedValue(value as T)
            }
        }

        override fun toString() = "SQSCancellationHandler[$segment, $index]"
    }
}

/**
 * Tries to resume this continuation atomically,
 * returns `true` if succeeds and `false` otherwise.
 */
private fun <T> CancellableContinuation<T>.tryResume0(value: T): Boolean {
    val token = tryResume(value) ?: return false
    completeResume(token)
    return true
}

private fun createSegment(id: Long, prev: SQSSegment?) = SQSSegment(id, prev, 0)

/**
 * The queue of waiters in [SegmentQueueSynchronizerJVM]
 * is represented as a linked list of these segments.
 */
private class SQSSegment(id: Long, prev: SQSSegment?, pointers: Int) : Segment<SQSSegment>(id, prev, pointers) {
    private val waiters = atomicArrayOfNulls<Any?>(SEGMENT_SIZE)
    override val maxSlots: Int get() = SEGMENT_SIZE

    @Suppress("NOTHING_TO_INLINE")
    inline fun get(index: Int): Any? = waiters[index].value

    @Suppress("NOTHING_TO_INLINE")
    inline fun set(index: Int, value: Any?) {
        waiters[index].value = value
    }

    @Suppress("NOTHING_TO_INLINE")
    inline fun cas(index: Int, expected: Any?, value: Any?): Boolean = waiters[index].compareAndSet(expected, value)

    @Suppress("NOTHING_TO_INLINE")
    inline fun getAndSet(index: Int, value: Any?): Any? = waiters[index].getAndSet(value)

    /**
     * Marks the cell as cancelled and returns `null`, so that
     * the [resume] that comes to the cell should notice
     * that the cell is cancelled and should fail or skip it
     * depending on the cancellation mode. However, in [SMART_ASYNC]
     * cancellation mode [resume] that comes to the cell with cancelled
     * continuation asynchronously puts its value into the cell,
     * and the cancellation handler completes the resumption.
     * In this case, [markCancelled] returns this non-null value.
     *
     * If the whole segment contains [CANCELLED] markers after
     * this invocation, [onSlotCleaned] is invoked and this segment
     * is going to be removed if [head][SegmentQueueSynchronizerJVM.head]
     * and [tail][SegmentQueueSynchronizerJVM.tail] do not reference it.
     * Note that the segments that are not stored physically are still
     * considered as logically stored but being full of cancelled waiters.
     */
    fun markCancelled(index: Int): Any? = mark(index, CANCELLED).also {
        onSlotCleaned()
    }

    /**
     * Marks the cell as refused and returns `null`, so that
     * the [resume] that comes to the cell should notice
     * that its value is refused by the [SegmentQueueSynchronizerJVM],
     * and [SegmentQueueSynchronizerJVM.tryReturnRefusedValue]
     * is invoked in this case (if it fails, the value is put back via
     * [SegmentQueueSynchronizerJVM.returnValue]). Since in [SMART_ASYNC]
     * cancellation mode [resume] that comes to the cell with cancelled
     * continuation asynchronously puts its value into the cell.
     * In this case, [markRefused] returns this non-null value.
     */
    fun markRefused(index: Int): Any? = mark(index, REFUSE)

    /**
     * Marks the cell with the specified [marker]
     * and returns `null` if the cell contains the
     * cancelled continuation. However, in the [SMART_ASYNC]
     * cancellation mode it is possible that [resume] comes
     * to the cell with cancelled continuation and asynchronously
     * puts its value into the cell, so that the cancellation
     * handler decides whether this value should be used for
     * resuming the next waiter or be refused. In the latter case,
     * the corresponding non-null value is returned as a result.
     */
    private fun mark(index: Int, marker: Any?): Any? =
        when (val old = getAndSet(index, marker)) {
            // Did the cell contain the cancelled continuation?
            is Continuation<*> -> {
                assert { if (old is CancellableContinuation<*>) old.isCancelled else true }
                null
            }
            // Did the cell contain an asynchronously put value?
            // (both branches deal with values)
            is WrappedContinuationValue -> old.cont
            else -> old
        }

    override fun toString() = "SQSSegment[id=$id, hashCode=${hashCode()}]"
}

/**
 * In the [smart asynchronous cancellation mode][SegmentQueueSynchronizerJVM.CancellationMode.SMART_ASYNC]
 * it is possible that [resume] comes to the cell with cancelled continuation and
 * asynchronously puts its value into the cell, so that the cancellation handler decides whether
 * this value should be used for resuming the next waiter or be refused. When this
 * value is a continuation, it is hard to distinguish it with the one related to the cancelled
 * waiter. Thus, such values are wrapped with [WrappedContinuationValue] in this case. Note, that the
 * wrapper is required only in [SegmentQueueSynchronizerJVM.CancellationMode.SMART_ASYNC] mode
 * and is used in the asynchronous race resolution logic between cancellation and [resume]
 * invocation; this way, it is used relatively rare.
 */
private class WrappedContinuationValue(val cont: Continuation<*>)

private val SEGMENT_SIZE = systemProp("kotlinx.coroutines.sqs.segmentSize", 16)
private val MAX_SPIN_CYCLES = systemProp("kotlinx.coroutines.sqs.maxSpinCycles", 100)
private val TAKEN = Symbol("TAKEN")
private val BROKEN = Symbol("BROKEN")
private val CANCELLED = Symbol("CANCELLED")
private val REFUSE = Symbol("REFUSE")
private val RESUMED = Symbol("RESUMED")

private const val TRY_RESUME_SUCCESS = 0
private const val TRY_RESUME_FAIL_CANCELLED = 1
private const val TRY_RESUME_FAIL_BROKEN = 2