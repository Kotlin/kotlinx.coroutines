/*
 * Copyright 2016-2024 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlin.math.min
import kotlin.wasm.WasmImport
import kotlin.wasm.unsafe.MemoryAllocator
import kotlin.wasm.unsafe.Pointer
import kotlin.wasm.unsafe.UnsafeWasmMemoryApi
import kotlin.wasm.unsafe.withScopedMemoryAllocator

@WasmImport("wasi_snapshot_preview1", "poll_oneoff")
private external fun wasiPollOneOff(ptrToSubscription: Int, eventPtr: Int, nsubscriptions: Int, resultPtr: Int): Int

@WasmImport("wasi_snapshot_preview1", "clock_time_get")
private external fun wasiRawClockTimeGet(clockId: Int, precision: Long, resultPtr: Int): Int

private const val CLOCKID_MONOTONIC = 1

internal class Event internal constructor(internal var callback: (() -> Unit)?, internal val absoluteTimeout: Long) {
    fun cancel() {
        if (callback == null) return
        callback = null
        nextCycleNearestEventAbsoluteTime = 0
        nextCycleContainTimedEvent = true
    }

    companion object {
        fun createCancelled(): Event = Event(null, 0)
    }
}

private var currentCycleEvents = mutableListOf<Event>()
private var nextCycleEvents = mutableListOf<Event>()
private var thrownExceptions = mutableListOf<Throwable>()
private var nextCycleNearestEventAbsoluteTime: Long = Long.MAX_VALUE
private var nextCycleContainTimedEvent = false

@OptIn(UnsafeWasmMemoryApi::class)
private fun initializeSubscriptionPtr(allocator: MemoryAllocator): Pointer {
    val ptrToSubscription = allocator.allocate(48)
    //userdata
    ptrToSubscription.storeLong(0)
    //uint8_t tag;
    (ptrToSubscription + 8).storeByte(0) //EVENTTYPE_CLOCK
    //__wasi_clockid_t id;
    (ptrToSubscription + 16).storeInt(CLOCKID_MONOTONIC) //CLOCKID_MONOTONIC
    //__wasi_timestamp_t timeout;
    //(ptrToSubscription + 24).storeLong(timeout)
    //__wasi_timestamp_t precision;
    (ptrToSubscription + 32).storeLong(0)
    //__wasi_subclockflags_t
    (ptrToSubscription + 40).storeShort(0) //ABSOLUTE_TIME=1/RELATIVE=0

    return ptrToSubscription
}

@OptIn(UnsafeWasmMemoryApi::class)
private fun clockTimeGet(ptrTo8Bytes: Pointer): Long {
    val returnCode = wasiRawClockTimeGet(
        clockId = CLOCKID_MONOTONIC,
        precision = 1,
        resultPtr = ptrTo8Bytes.address.toInt()
    )
    check(returnCode == 0)
    return ptrTo8Bytes.loadLong()
}

@OptIn(UnsafeWasmMemoryApi::class)
private fun sleep(timeout: Long, ptrTo32Bytes: Pointer, ptrTo8Bytes: Pointer, ptrToSubscription: Pointer) {
    //__wasi_timestamp_t timeout;
    (ptrToSubscription + 24).storeLong(timeout)

    val returnCode = wasiPollOneOff(
        ptrToSubscription = ptrToSubscription.address.toInt(),
        eventPtr = ptrTo32Bytes.address.toInt(),
        nsubscriptions = 1,
        resultPtr = ptrTo8Bytes.address.toInt()
    )

    check(returnCode == 0)
}

@OptIn(UnsafeWasmMemoryApi::class)
private fun sleepAndGetTime(
    absoluteTime: Long,
    ptrTo32Bytes: Pointer,
    ptrTo8Bytes: Pointer,
    ptrToSubscription: Pointer
): Long {
    var currentTime = clockTimeGet(ptrTo8Bytes)
    val sleepTimeout = absoluteTime - currentTime

    if (sleepTimeout > 0) {
        sleep(
            timeout = sleepTimeout,
            ptrTo32Bytes = ptrTo32Bytes,
            ptrTo8Bytes = ptrTo8Bytes,
            ptrToSubscription = ptrToSubscription
        )
        currentTime += sleepTimeout
    }

    return currentTime
}

private fun runEventCycleSimple() {
    for (currentEvent in currentCycleEvents) {
        try {
            currentEvent.callback?.invoke()
        } catch (e: Throwable) {
            thrownExceptions.add(e)
        }
    }
}

private fun runEventCycle(currentTime: Long) {
    for (currentEvent in currentCycleEvents) {
        val callback = currentEvent.callback ?: continue
        val eventAbsoluteTime = currentEvent.absoluteTimeout
        if (currentTime >= eventAbsoluteTime) {
            try {
                callback()
            } catch (e: Throwable) {
                thrownExceptions.add(e)
            }
        } else {
            nextCycleEvents.add(currentEvent)
            nextCycleNearestEventAbsoluteTime = min(eventAbsoluteTime, nextCycleNearestEventAbsoluteTime)
            nextCycleContainTimedEvent = eventAbsoluteTime > 0
        }
    }
}

@OptIn(UnsafeWasmMemoryApi::class)
internal fun runEventLoop() {
    if (nextCycleEvents.isEmpty()) return

    withScopedMemoryAllocator { allocator ->
        val ptrTo32Bytes = allocator.allocate(32)
        val ptrTo8Bytes = allocator.allocate(8)
        val ptrToSubscription = initializeSubscriptionPtr(allocator)

        while (nextCycleEvents.isNotEmpty()) {
            val currentNextEventTime = nextCycleNearestEventAbsoluteTime

            val buffer = currentCycleEvents
            currentCycleEvents = nextCycleEvents
            nextCycleEvents = buffer
            nextCycleEvents.clear()
            nextCycleNearestEventAbsoluteTime = Long.MAX_VALUE

            if (nextCycleContainTimedEvent) {
                nextCycleContainTimedEvent = false

                val currentTime = sleepAndGetTime(
                    absoluteTime = currentNextEventTime,
                    ptrTo32Bytes = ptrTo32Bytes,
                    ptrTo8Bytes = ptrTo8Bytes,
                    ptrToSubscription = ptrToSubscription
                )
                runEventCycle(currentTime = currentTime)
            } else {
                runEventCycleSimple()
            }
        }
    }

    if (thrownExceptions.isNotEmpty()) {
        val exceptionToThrow = thrownExceptions.singleOrNull() ?: EventLoopException(thrownExceptions.toList())
        thrownExceptions.clear()
        throw exceptionToThrow
    }
}

/* Register new event with specified timeout in nanoseconds */
@OptIn(UnsafeWasmMemoryApi::class)
internal fun registerEvent(timeout: Long, callback: () -> Unit): Event {
    if (kotlin.wasm.internal.onExportedFunctionExit == null) {
        kotlin.wasm.internal.onExportedFunctionExit = ::runEventLoop
    }

    require(timeout >= 0L) { "Timeout cannot be negative" }
    val taskAbsoluteTime: Long
    if (timeout > 0L) {
        val absoluteCurrentTime = withScopedMemoryAllocator { allocator ->
            clockTimeGet(ptrTo8Bytes = allocator.allocate(8))
        }
        taskAbsoluteTime = absoluteCurrentTime + timeout
        if (taskAbsoluteTime <= 0) return Event.createCancelled()
        nextCycleNearestEventAbsoluteTime = min(taskAbsoluteTime, nextCycleNearestEventAbsoluteTime)
        nextCycleContainTimedEvent = true

    } else {
        taskAbsoluteTime = 0
        nextCycleNearestEventAbsoluteTime = 0
    }

    val event = Event(callback, taskAbsoluteTime)
    nextCycleEvents.add(event)
    return event
}