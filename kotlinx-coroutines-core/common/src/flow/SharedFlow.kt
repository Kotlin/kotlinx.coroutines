/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.internal.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.jvm.*
import kotlin.native.concurrent.*

/**
 * A _hot_ [Flow] that shares emitted values among all its collectors in a broadcast fashion, so that all collectors
 * get all emitted values. A shared flow is called _hot_ because its active instance exists independently of the
 * presence of collectors. This is opposed to a regular [Flow], such as defined by the [`flow { ... }`][flow] function,
 * which is _cold_ and is started separately for each collector.
 *
 * **Shared flow never completes**. A call to [Flow.collect] on a shared flow never completes normally, and
 * neither does a coroutine started by the [Flow.launchIn] function. An active collector of a shared flow is called a _subscriber_.
 *
 * A subscriber of a shared flow can be cancelled. This usually happens when the scope in which the coroutine is running
 * is cancelled. A subscriber to a shared flow is always [cancellable][Flow.cancellable], and checks for
 * cancellation before each emission. Note that most terminal operators like [Flow.toList] would also not complete,
 * when applied to a shared flow, but flow-truncating operators like [Flow.take] and [Flow.takeWhile] can be used on a
 * shared flow to turn it into a completing one.
 *
 * A [mutable shared flow][MutableSharedFlow] is created using the [MutableSharedFlow(...)] constructor function.
 * Its state can be updated by [emitting][MutableSharedFlow.emit] values to it and performing other operations.
 * See the [MutableSharedFlow] documentation for details.
 *
 * [SharedFlow] is useful for broadcasting events that happen inside an application to subscribers that can come and go.
 * For example, the following class encapsulates an event bus that distributes events to all subscribers
 * in a _rendezvous_ manner, suspending until all subscribers receive emitted event:
 *
 * ```
 * class EventBus {
 *     private val _events = MutableSharedFlow<Event>() // private mutable shared flow
 *     val events = _events.asSharedFlow() // publicly exposed as read-only shared flow
 *
 *     suspend fun produceEvent(event: Event) {
 *         _events.emit(event) // suspends until all subscribers receive it
 *     }
 * }
 * ```
 *
 * As an alternative to the above usage with the `MutableSharedFlow(...)` constructor function,
 * any _cold_ [Flow] can be converted to a shared flow using the [shareIn] operator.
 *
 * There is a specialized implementation of shared flow for the case where the most recent state value needs
 * to be shared. See [StateFlow] for details.
 *
 * ### Replay cache and buffer
 *
 * A shared flow keeps a specific number of the most recent values in its _replay cache_. Every new subscriber first
 * gets the values from the replay cache and then gets new emitted values. The maximum size of the replay cache is
 * specified when the shared flow is created by the `replay` parameter. A snapshot of the current replay cache
 * is available via the [replayCache] property and it can be reset with the [MutableSharedFlow.resetReplayCache] function.
 *
 * A replay cache also provides buffer for emissions to the shared flow, allowing slow subscribers to
 * get values from the buffer without suspending emitters. The buffer space determines how much slow subscribers
 * can lag from the fast ones. When creating a shared flow, additional buffer capacity beyond replay can be reserved
 * using the `extraBufferCapacity` parameter.
 * 
 * A shared flow with a buffer can be configured to avoid suspension of emitters on buffer overflow using
 * the `onBufferOverflow` parameter, which is equal to one of the entries of the [BufferOverflow] enum. When a strategy other
 * than [SUSPENDED][BufferOverflow.SUSPEND] is configured, emissions to the shared flow never suspend.
 *
 * **Buffer overflow condition can happen only when there is at least one subscriber that is not ready to accept
 * the new value.**  In the absence of subscribers only the most recent `replay` values are stored and the buffer
 * overflow behavior is never triggered and has no effect. In particular, in the absence of subscribers emitter never
 * suspends despite [BufferOverflow.SUSPEND] option and [BufferOverflow.DROP_LATEST] option does not have effect either.
 * Essentially, the behavior in the absence of subscribers is always similar to [BufferOverflow.DROP_OLDEST],
 * but the buffer is just of `replay` size (without any `extraBufferCapacity`).
 *
 * ### Unbuffered shared flow
 *
 * A default implementation of a shared flow that is created with `MutableSharedFlow()` constructor function
 * without parameters has no replay cache nor additional buffer.
 * [emit][MutableSharedFlow.emit] call to such a shared flow suspends until all subscribers receive the emitted value
 * and returns immediately if there are no subscribers.
 * Thus, [tryEmit][MutableSharedFlow.tryEmit] call succeeds and returns `true` only if
 * there are no subscribers (in which case the emitted value is immediately lost).
 *
 * ### SharedFlow vs BroadcastChannel
 *
 * Conceptually shared flow is similar to [BroadcastChannel][BroadcastChannel]
 * and is designed to completely replace it.
 * It has the following important differences:
 *
 * * `SharedFlow` is simpler, because it does not have to implement all the [Channel] APIs, which allows
 *    for faster and simpler implementation.
 * * `SharedFlow` supports configurable replay and buffer overflow strategy.
 * * `SharedFlow` has a clear separation into a read-only `SharedFlow` interface and a [MutableSharedFlow].
 * * `SharedFlow` cannot be closed like `BroadcastChannel` and can never represent a failure.
 *    All errors and completion signals should be explicitly _materialized_ if needed.
 *
 * To migrate [BroadcastChannel] usage to [SharedFlow], start by replacing usages of the `BroadcastChannel(capacity)`
 * constructor with `MutableSharedFlow(0, extraBufferCapacity=capacity)` (broadcast channel does not replay
 * values to new subscribers). Replace [send][BroadcastChannel.send] and [trySend][BroadcastChannel.trySend] calls
 * with [emit][MutableStateFlow.emit] and [tryEmit][MutableStateFlow.tryEmit], and convert subscribers' code to flow operators.
 *
 * ### Concurrency
 *
 * All methods of shared flow are **thread-safe** and can be safely invoked from concurrent coroutines without
 * external synchronization.
 *
 * ### Operator fusion
 *
 * Application of [flowOn][Flow.flowOn], [buffer] with [RENDEZVOUS][Channel.RENDEZVOUS] capacity,
 * or [cancellable] operators to a shared flow has no effect.
 *
 * ### Implementation notes
 *
 * Shared flow implementation uses a lock to ensure thread-safety, but suspending collector and emitter coroutines are
 * resumed outside of this lock to avoid dead-locks when using unconfined coroutines. Adding new subscribers
 * has `O(1)` amortized cost, but emitting has `O(N)` cost, where `N` is the number of subscribers.
 *
 * ### Not stable for inheritance
 *
 * **The `SharedFlow` interface is not stable for inheritance in 3rd party libraries**, as new methods
 * might be added to this interface in the future, but is stable for use.
 * Use the `MutableSharedFlow(replay, ...)` constructor function to create an implementation.
 */
public interface SharedFlow<out T> : Flow<T> {
    /**
     * A snapshot of the replay cache.
     */
    public val replayCache: List<T>
}

/**
 * A mutable [SharedFlow] that provides functions to [emit] values to the flow.
 * An instance of `MutableSharedFlow` with the given configuration parameters can be created using `MutableSharedFlow(...)`
 * constructor function.
 *
 * See the [SharedFlow] documentation for details on shared flows.
 *
 * `MutableSharedFlow` is a [SharedFlow] that also provides the abilities to [emit] a value,
 * to [tryEmit] without suspension if possible, to track the [subscriptionCount],
 * and to [resetReplayCache].
 *
 * ### Concurrency
 *
 * All methods of shared flow are **thread-safe** and can be safely invoked from concurrent coroutines without
 * external synchronization.
 *
 * ### Not stable for inheritance
 *
 * **The `MutableSharedFlow` interface is not stable for inheritance in 3rd party libraries**, as new methods
 * might be added to this interface in the future, but is stable for use.
 * Use the `MutableSharedFlow(...)` constructor function to create an implementation.
 */
public interface MutableSharedFlow<T> : SharedFlow<T>, FlowCollector<T> {
    /**
     * Emits a [value] to this shared flow, suspending on buffer overflow if the shared flow was created
     * with the default [BufferOverflow.SUSPEND] strategy.
     *
     * See [tryEmit] for a non-suspending variant of this function.
     *
     * This method is **thread-safe** and can be safely invoked from concurrent coroutines without
     * external synchronization.
     */
    override suspend fun emit(value: T)

    /**
     * Tries to emit a [value] to this shared flow without suspending. It returns `true` if the value was
     * emitted successfully. When this function returns `false`, it means that the call to a plain [emit]
     * function will suspend until there is a buffer space available.
     *
     * A shared flow configured with a [BufferOverflow] strategy other than [SUSPEND][BufferOverflow.SUSPEND]
     * (either [DROP_OLDEST][BufferOverflow.DROP_OLDEST] or [DROP_LATEST][BufferOverflow.DROP_LATEST]) never
     * suspends on [emit], and thus `tryEmit` to such a shared flow always returns `true`.
     *
     * This method is **thread-safe** and can be safely invoked from concurrent coroutines without
     * external synchronization.
     */
    public fun tryEmit(value: T): Boolean

    /**
     * The number of subscribers (active collectors) to this shared flow.
     *
     * The integer in the resulting [StateFlow] is not negative and starts with zero for a freshly created
     * shared flow.
     *
     * This state can be used to react to changes in the number of subscriptions to this shared flow.
     * For example, if you need to call `onActive` when the first subscriber appears and `onInactive`
     * when the last one disappears, you can set it up like this:
     *
     * ```
     * sharedFlow.subscriptionCount
     *     .map { count -> count > 0 } // map count into active/inactive flag
     *     .distinctUntilChanged() // only react to true<->false changes
     *     .onEach { isActive -> // configure an action
     *         if (isActive) onActive() else onInactive()
     *     }
     *     .launchIn(scope) // launch it
     * ```
     */
    public val subscriptionCount: StateFlow<Int>

    /**
     * Resets the [replayCache] of this shared flow to an empty state.
     * New subscribers will be receiving only the values that were emitted after this call,
     * while old subscribers will still be receiving previously buffered values.
     * To reset a shared flow to an initial value, emit the value after this call.
     *
     * On a [MutableStateFlow], which always contains a single value, this function is not
     * supported, and throws an [UnsupportedOperationException]. To reset a [MutableStateFlow]
     * to an initial value, just update its [value][MutableStateFlow.value].
     *
     * This method is **thread-safe** and can be safely invoked from concurrent coroutines without
     * external synchronization.
     *
     * **Note: This is an experimental api.** This function may be removed or renamed in the future.
     */
    @ExperimentalCoroutinesApi
    public fun resetReplayCache()
}

/**
 * Creates a [MutableSharedFlow] with the given configuration parameters.
 *
 * This function throws [IllegalArgumentException] on unsupported values of parameters or combinations thereof.
 *
 * @param replay the number of values replayed to new subscribers (cannot be negative, defaults to zero).
 * @param extraBufferCapacity the number of values buffered in addition to `replay`.
 *   [emit][MutableSharedFlow.emit] does not suspend while there is a buffer space remaining (optional, cannot be negative, defaults to zero).
 * @param onBufferOverflow configures an [emit][MutableSharedFlow.emit] action on buffer overflow. Optional, defaults to
 *   [suspending][BufferOverflow.SUSPEND] attempts to emit a value.
 *   Values other than [BufferOverflow.SUSPEND] are supported only when `replay > 0` or `extraBufferCapacity > 0`.
 *   **Buffer overflow can happen only when there is at least one subscriber that is not ready to accept
 *   the new value.** In the absence of subscribers only the most recent [replay] values are stored and
 *   the buffer overflow behavior is never triggered and has no effect.
 */
@Suppress("FunctionName", "UNCHECKED_CAST")
public fun <T> MutableSharedFlow(
    replay: Int = 0,
    extraBufferCapacity: Int = 0,
    onBufferOverflow: BufferOverflow = BufferOverflow.SUSPEND
): MutableSharedFlow<T> {
    require(replay >= 0) { "replay cannot be negative, but was $replay" }
    require(extraBufferCapacity >= 0) { "extraBufferCapacity cannot be negative, but was $extraBufferCapacity" }
    require(replay > 0 || extraBufferCapacity > 0 || onBufferOverflow == BufferOverflow.SUSPEND) {
        "replay or extraBufferCapacity must be positive with non-default onBufferOverflow strategy $onBufferOverflow"
    }
    val bufferCapacity0 = replay + extraBufferCapacity
    val bufferCapacity = if (bufferCapacity0 < 0) Int.MAX_VALUE else bufferCapacity0 // coerce to MAX_VALUE on overflow
    return SharedFlowImpl(replay, bufferCapacity, onBufferOverflow)
}

// ------------------------------------ Implementation ------------------------------------

private class SharedFlowSlot : AbstractSharedFlowSlot<SharedFlowImpl<*>>() {
    @JvmField
    var index = -1L // current "to-be-emitted" index, -1 means the slot is free now

    @JvmField
    var cont: Continuation<Unit>? = null // collector waiting for new value

    override fun allocateLocked(flow: SharedFlowImpl<*>): Boolean {
        if (index >= 0) return false // not free
        index = flow.updateNewCollectorIndexLocked()
        return true
    }

    override fun freeLocked(flow: SharedFlowImpl<*>): Array<Continuation<Unit>?> {
        assert { index >= 0 }
        val oldIndex = index
        index = -1L
        cont = null // cleanup continuation reference
        return flow.updateCollectorIndexLocked(oldIndex)
    }
}

private class SharedFlowImpl<T>(
    private val replay: Int,
    private val bufferCapacity: Int,
    private val onBufferOverflow: BufferOverflow
) : AbstractSharedFlow<SharedFlowSlot>(), MutableSharedFlow<T>, CancellableFlow<T>, FusibleFlow<T> {
    /*
        Logical structure of the buffer

                  buffered values
             /-----------------------\
                          replayCache      queued emitters
                          /----------\/----------------------\
         +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
         |   | 1 | 2 | 3 | 4 | 5 | 6 | E | E | E | E | E | E |   |   |   |
         +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
               ^           ^           ^                      ^
               |           |           |                      |
              head         |      head + bufferSize     head + totalSize
               |           |           |
     index of the slowest  |    index of the fastest
      possible collector   |     possible collector
               |           |
               |     replayIndex == new collector's index
               \---------------------- /
          range of possible minCollectorIndex

          head == minOf(minCollectorIndex, replayIndex) // by definition
          totalSize == bufferSize + queueSize // by definition

       INVARIANTS:
          minCollectorIndex = activeSlots.minOf { it.index } ?: (head + bufferSize)
          replayIndex <= head + bufferSize
     */

    // Stored state
    private var buffer: Array<Any?>? = null // allocated when needed, allocated size always power of two
    private var replayIndex = 0L // minimal index from which new collector gets values
    private var minCollectorIndex = 0L // minimal index of active collectors, equal to replayIndex if there are none
    private var bufferSize = 0 // number of buffered values
    private var queueSize = 0 // number of queued emitters

    // Computed state
    private val head: Long get() = minOf(minCollectorIndex, replayIndex)
    private val replaySize: Int get() = (head + bufferSize - replayIndex).toInt()
    private val totalSize: Int get() = bufferSize + queueSize
    private val bufferEndIndex: Long get() = head + bufferSize
    private val queueEndIndex: Long get() = head + bufferSize + queueSize

    override val replayCache: List<T>
        get() = synchronized(this) {
            val replaySize = this.replaySize
            if (replaySize == 0) return emptyList()
            val result = ArrayList<T>(replaySize)
            val buffer = buffer!! // must be allocated, because replaySize > 0
            @Suppress("UNCHECKED_CAST")
            for (i in 0 until replaySize) result += buffer.getBufferAt(replayIndex + i) as T
            result
        }

    @Suppress("UNCHECKED_CAST")
    override suspend fun collect(collector: FlowCollector<T>) {
        val slot = allocateSlot()
        try {
            if (collector is SubscribedFlowCollector) collector.onSubscription()
            val collectorJob = currentCoroutineContext()[Job]
            while (true) {
                var newValue: Any?
                while (true) {
                    newValue = tryTakeValue(slot) // attempt no-suspend fast path first
                    if (newValue !== NO_VALUE) break
                    awaitValue(slot) // await signal that the new value is available
                }
                collectorJob?.ensureActive()
                collector.emit(newValue as T)
            }
        } finally {
            freeSlot(slot)
        }
    }

    override fun tryEmit(value: T): Boolean {
        var resumes: Array<Continuation<Unit>?> = EMPTY_RESUMES
        val emitted = synchronized(this) {
            if (tryEmitLocked(value)) {
                resumes = findSlotsToResumeLocked(resumes)
                true
            } else {
                false
            }
        }
        for (cont in resumes) cont?.resume(Unit)
        return emitted
    }

    override suspend fun emit(value: T) {
        if (tryEmit(value)) return // fast-path
        emitSuspend(value)
    }

    @Suppress("UNCHECKED_CAST")
    private fun tryEmitLocked(value: T): Boolean {
        // Fast path without collectors -> no buffering
        if (nCollectors == 0) return tryEmitNoCollectorsLocked(value) // always returns true
        // With collectors we'll have to buffer
        // cannot emit now if buffer is full & blocked by slow collectors
        if (bufferSize >= bufferCapacity && minCollectorIndex <= replayIndex) {
            when (onBufferOverflow) {
                BufferOverflow.SUSPEND -> return false // will suspend
                BufferOverflow.DROP_LATEST -> return true // just drop incoming
                BufferOverflow.DROP_OLDEST -> {} // force enqueue & drop oldest instead
            }
        }
        enqueueLocked(value)
        bufferSize++ // value was added to buffer
        // drop oldest from the buffer if it became more than bufferCapacity
        if (bufferSize > bufferCapacity) dropOldestLocked()
        // keep replaySize not larger that needed
        if (replaySize > replay) { // increment replayIndex by one
            updateBufferLocked(replayIndex + 1, minCollectorIndex, bufferEndIndex, queueEndIndex)
        }
        return true
    }

    private fun tryEmitNoCollectorsLocked(value: T): Boolean {
        assert { nCollectors == 0 }
        if (replay == 0) return true // no need to replay, just forget it now
        enqueueLocked(value) // enqueue to replayCache
        bufferSize++ // value was added to buffer
        // drop oldest from the buffer if it became more than replay
        if (bufferSize > replay) dropOldestLocked()
        minCollectorIndex = head + bufferSize // a default value (max allowed)
        return true
    }

    private fun dropOldestLocked() {
        buffer!!.setBufferAt(head, null)
        bufferSize--
        val newHead = head + 1
        if (replayIndex < newHead) replayIndex = newHead
        if (minCollectorIndex < newHead) correctCollectorIndexesOnDropOldest(newHead)
        assert { head == newHead } // since head = minOf(minCollectorIndex, replayIndex) it should have updated
    }

    private fun correctCollectorIndexesOnDropOldest(newHead: Long) {
        forEachSlotLocked { slot ->
            @Suppress("ConvertTwoComparisonsToRangeCheck") // Bug in JS backend
            if (slot.index >= 0 && slot.index < newHead) {
                slot.index = newHead // force move it up (this collector was too slow and missed the value at its index)
            }
        }
        minCollectorIndex = newHead
    }

    // enqueues item to buffer array, caller shall increment either bufferSize or queueSize
    private fun enqueueLocked(item: Any?) {
        val curSize = totalSize
        val buffer = when (val curBuffer = buffer) {
            null -> growBuffer(null, 0, 2)
            else -> if (curSize >= curBuffer.size) growBuffer(curBuffer, curSize,curBuffer.size * 2) else curBuffer
        }
        buffer.setBufferAt(head + curSize, item)
    }

    private fun growBuffer(curBuffer: Array<Any?>?, curSize: Int, newSize: Int): Array<Any?> {
        check(newSize > 0) { "Buffer size overflow" }
        val newBuffer = arrayOfNulls<Any?>(newSize).also { buffer = it }
        if (curBuffer == null) return newBuffer
        val head = head
        for (i in 0 until curSize) {
            newBuffer.setBufferAt(head + i, curBuffer.getBufferAt(head + i))
        }
        return newBuffer
    }

    private suspend fun emitSuspend(value: T) = suspendCancellableCoroutine<Unit> sc@{ cont ->
        var resumes: Array<Continuation<Unit>?> = EMPTY_RESUMES
        val emitter = synchronized(this) lock@{
            // recheck buffer under lock again (make sure it is really full)
            if (tryEmitLocked(value)) {
                cont.resume(Unit)
                resumes = findSlotsToResumeLocked(resumes)
                return@lock null
            }
            // add suspended emitter to the buffer
            Emitter(this, head + totalSize, value, cont).also {
                enqueueLocked(it)
                queueSize++ // added to queue of waiting emitters
                // synchronous shared flow might rendezvous with waiting emitter
                if (bufferCapacity == 0) resumes = findSlotsToResumeLocked(resumes)
            }
        }
        // outside of the lock: register dispose on cancellation
        emitter?.let { cont.disposeOnCancellation(it) }
        // outside of the lock: resume slots if needed
        for (r in resumes) r?.resume(Unit)
    }

    private fun cancelEmitter(emitter: Emitter) = synchronized(this) {
        if (emitter.index < head) return // already skipped past this index
        val buffer = buffer!!
        if (buffer.getBufferAt(emitter.index) !== emitter) return // already resumed
        buffer.setBufferAt(emitter.index, NO_VALUE)
        cleanupTailLocked()
    }

    internal fun updateNewCollectorIndexLocked(): Long {
        val index = replayIndex
        if (index < minCollectorIndex) minCollectorIndex = index
        return index
    }

    // Is called when a collector disappears or changes index, returns a list of continuations to resume after lock
    internal fun updateCollectorIndexLocked(oldIndex: Long): Array<Continuation<Unit>?> {
        assert { oldIndex >= minCollectorIndex }
        if (oldIndex > minCollectorIndex) return EMPTY_RESUMES // nothing changes, it was not min
        // start computing new minimal index of active collectors
        val head = head
        var newMinCollectorIndex = head + bufferSize
        // take into account a special case of sync shared flow that can go past 1st queued emitter
        if (bufferCapacity == 0 && queueSize > 0) newMinCollectorIndex++
        forEachSlotLocked { slot ->
            @Suppress("ConvertTwoComparisonsToRangeCheck") // Bug in JS backend
            if (slot.index >= 0 && slot.index < newMinCollectorIndex) newMinCollectorIndex = slot.index
        }
        assert { newMinCollectorIndex >= minCollectorIndex } // can only grow
        if (newMinCollectorIndex <= minCollectorIndex) return EMPTY_RESUMES // nothing changes
        // Compute new buffer size if we drop items we no longer need and no emitter is resumed:
        // We must keep all the items from newMinIndex to the end of buffer
        var newBufferEndIndex = bufferEndIndex // var to grow when waiters are resumed
        val maxResumeCount = if (nCollectors > 0) {
            // If we have collectors we can resume up to maxResumeCount waiting emitters
            // a) queueSize -> that's how many waiting emitters we have
            // b) bufferCapacity - newBufferSize0 -> that's how many we can afford to resume to add w/o exceeding bufferCapacity
            val newBufferSize0 = (newBufferEndIndex - newMinCollectorIndex).toInt()
            minOf(queueSize, bufferCapacity - newBufferSize0)
        } else {
            // If we don't have collectors anymore we must resume all waiting emitters
            queueSize // that's how many waiting emitters we have (at most)
        }
        var resumes: Array<Continuation<Unit>?> = EMPTY_RESUMES
        val newQueueEndIndex = newBufferEndIndex + queueSize
        if (maxResumeCount > 0) { // collect emitters to resume if we have them
            resumes = arrayOfNulls(maxResumeCount)
            var resumeCount = 0
            val buffer = buffer!!
            for (curEmitterIndex in newBufferEndIndex until newQueueEndIndex) {
                val emitter = buffer.getBufferAt(curEmitterIndex)
                if (emitter !== NO_VALUE) {
                    emitter as Emitter // must have Emitter class
                    resumes[resumeCount++] = emitter.cont
                    buffer.setBufferAt(curEmitterIndex, NO_VALUE) // make as canceled if we moved ahead
                    buffer.setBufferAt(newBufferEndIndex, emitter.value)
                    newBufferEndIndex++
                    if (resumeCount >= maxResumeCount) break // enough resumed, done
                }
            }
        }
        // Compute new buffer size -> how many values we now actually have after resume
        val newBufferSize1 = (newBufferEndIndex - head).toInt()
        // Note: When nCollectors == 0 we resume ALL queued emitters and we might have resumed more than bufferCapacity,
        // and newMinCollectorIndex might pointing the wrong place because of that. The easiest way to fix it is by
        // forcing newMinCollectorIndex = newBufferEndIndex. We do not needed to update newBufferSize1 (which could be
        // too big), because the only use of newBufferSize1 in the below code is in the minOf(replay, newBufferSize1)
        // expression, which coerces values that are too big anyway.
        if (nCollectors == 0) newMinCollectorIndex = newBufferEndIndex
        // Compute new replay size -> limit to replay the number of items we need, take into account that it can only grow
        var newReplayIndex = maxOf(replayIndex, newBufferEndIndex - minOf(replay, newBufferSize1))
        // adjustment for synchronous case with cancelled emitter (NO_VALUE)
        if (bufferCapacity == 0 && newReplayIndex < newQueueEndIndex && buffer!!.getBufferAt(newReplayIndex) == NO_VALUE) {
            newBufferEndIndex++
            newReplayIndex++
        }
        // Update buffer state
        updateBufferLocked(newReplayIndex, newMinCollectorIndex, newBufferEndIndex, newQueueEndIndex)
        // just in case we've moved all buffered emitters and have NO_VALUE's at the tail now
        cleanupTailLocked()
        // We need to waken up suspended collectors if any emitters were resumed here
        if (resumes.isNotEmpty()) resumes = findSlotsToResumeLocked(resumes)
        return resumes
    }

    private fun updateBufferLocked(
        newReplayIndex: Long,
        newMinCollectorIndex: Long,
        newBufferEndIndex: Long,
        newQueueEndIndex: Long
    ) {
        // Compute new head value
        val newHead = minOf(newMinCollectorIndex, newReplayIndex)
        assert { newHead >= head }
        // cleanup items we don't have to buffer anymore (because head is about to move)
        for (index in head until newHead) buffer!!.setBufferAt(index, null)
        // update all state variables to newly computed values
        replayIndex = newReplayIndex
        minCollectorIndex = newMinCollectorIndex
        bufferSize = (newBufferEndIndex - newHead).toInt()
        queueSize = (newQueueEndIndex - newBufferEndIndex).toInt()
        // check our key invariants (just in case)
        assert { bufferSize >= 0 }
        assert { queueSize >= 0 }
        assert { replayIndex <= this.head + bufferSize }
    }

    // Removes all the NO_VALUE items from the end of the queue and reduces its size
    private fun cleanupTailLocked() {
        // If we have synchronous case, then keep one emitter queued
        if (bufferCapacity == 0 && queueSize <= 1) return // return, don't clear it
        val buffer = buffer!!
        while (queueSize > 0 && buffer.getBufferAt(head + totalSize - 1) === NO_VALUE) {
            queueSize--
            buffer.setBufferAt(head + totalSize, null)
        }
    }

    // returns NO_VALUE if cannot take value without suspension
    private fun tryTakeValue(slot: SharedFlowSlot): Any? {
        var resumes: Array<Continuation<Unit>?> = EMPTY_RESUMES
        val value = synchronized(this) {
            val index = tryPeekLocked(slot)
            if (index < 0) {
                NO_VALUE
            } else {
                val oldIndex = slot.index
                val newValue = getPeekedValueLockedAt(index)
                slot.index = index + 1 // points to the next index after peeked one
                resumes = updateCollectorIndexLocked(oldIndex)
                newValue
            }
        }
        for (resume in resumes) resume?.resume(Unit)
        return value
    }

    // returns -1 if cannot peek value without suspension
    private fun tryPeekLocked(slot: SharedFlowSlot): Long {
        // return buffered value if possible
        val index = slot.index
        if (index < bufferEndIndex) return index
        if (bufferCapacity > 0) return -1L // if there's a buffer, never try to rendezvous with emitters
        // Synchronous shared flow (bufferCapacity == 0) tries to rendezvous
        if (index > head) return -1L // ... but only with the first emitter (never look forward)
        if (queueSize == 0) return -1L // nothing there to rendezvous with
        return index // rendezvous with the first emitter
    }

    private fun getPeekedValueLockedAt(index: Long): Any? =
        when (val item = buffer!!.getBufferAt(index)) {
            is Emitter -> item.value
            else -> item
        }

    private suspend fun awaitValue(slot: SharedFlowSlot): Unit = suspendCancellableCoroutine { cont ->
        synchronized(this) lock@{
            val index = tryPeekLocked(slot) // recheck under this lock
            if (index < 0) {
                slot.cont = cont // Ok -- suspending
            } else {
                cont.resume(Unit) // has value, no need to suspend
                return@lock
            }
            slot.cont = cont // suspend, waiting
        }
    }

    private fun findSlotsToResumeLocked(resumesIn: Array<Continuation<Unit>?>): Array<Continuation<Unit>?> {
        var resumes: Array<Continuation<Unit>?> = resumesIn
        var resumeCount = resumesIn.size
        forEachSlotLocked loop@{ slot ->
            val cont = slot.cont ?: return@loop // only waiting slots
            if (tryPeekLocked(slot) < 0) return@loop // only slots that can peek a value
            if (resumeCount >= resumes.size) resumes = resumes.copyOf(maxOf(2, 2 * resumes.size))
            resumes[resumeCount++] = cont
            slot.cont = null // not waiting anymore
        }
        return resumes
    }

    override fun createSlot() = SharedFlowSlot()
    override fun createSlotArray(size: Int): Array<SharedFlowSlot?> = arrayOfNulls(size)

    override fun resetReplayCache() = synchronized(this) {
        // Update buffer state
        updateBufferLocked(
            newReplayIndex = bufferEndIndex,
            newMinCollectorIndex = minCollectorIndex,
            newBufferEndIndex = bufferEndIndex,
            newQueueEndIndex = queueEndIndex
        )
    }

    override fun fuse(context: CoroutineContext, capacity: Int, onBufferOverflow: BufferOverflow) =
        fuseSharedFlow(context, capacity, onBufferOverflow)
    
    private class Emitter(
        @JvmField val flow: SharedFlowImpl<*>,
        @JvmField var index: Long,
        @JvmField val value: Any?,
        @JvmField val cont: Continuation<Unit>
    ) : DisposableHandle {
        override fun dispose() = flow.cancelEmitter(this)
    }
}

@SharedImmutable
@JvmField
internal val NO_VALUE = Symbol("NO_VALUE")

private fun Array<Any?>.getBufferAt(index: Long) = get(index.toInt() and (size - 1))
private fun Array<Any?>.setBufferAt(index: Long, item: Any?) = set(index.toInt() and (size - 1), item)

internal fun <T> SharedFlow<T>.fuseSharedFlow(
    context: CoroutineContext,
    capacity: Int,
    onBufferOverflow: BufferOverflow
): Flow<T> {
    // context is irrelevant for shared flow and making additional rendezvous is meaningless
    // however, additional non-trivial buffering after shared flow could make sense for very slow subscribers
    if ((capacity == Channel.RENDEZVOUS || capacity == Channel.OPTIONAL_CHANNEL) && onBufferOverflow == BufferOverflow.SUSPEND) {
        return this
    }
    // Apply channel flow operator as usual
    return ChannelFlowOperatorImpl(this, context, capacity, onBufferOverflow)
}
