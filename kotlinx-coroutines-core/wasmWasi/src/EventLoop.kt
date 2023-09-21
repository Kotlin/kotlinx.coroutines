@file:OptIn(UnsafeWasmMemoryApi::class)
package kotlinx.coroutines

import kotlin.coroutines.CoroutineContext
import kotlin.wasm.*
import kotlin.wasm.unsafe.*

@WasmImport("wasi_snapshot_preview1", "poll_oneoff")
private external fun wasiPollOneOff(ptrToSubscription: Int, eventPtr: Int, nsubscriptions: Int, resultPtr: Int): Int

@WasmImport("wasi_snapshot_preview1", "clock_time_get")
private external fun wasiRawClockTimeGet(clockId: Int, precision: Long, resultPtr: Int): Int

private const val CLOCKID_MONOTONIC = 1

internal actual fun createEventLoop(): EventLoop = DefaultExecutor

internal actual fun nanoTime(): Long = withScopedMemoryAllocator { allocator: MemoryAllocator ->
    val ptrTo8Bytes = allocator.allocate(8)
    val returnCode = wasiRawClockTimeGet(
        clockId = CLOCKID_MONOTONIC,
        precision = 1,
        resultPtr = ptrTo8Bytes.address.toInt()
    )
    check(returnCode == 0) { "clock_time_get failed with the return code $returnCode" }
    ptrTo8Bytes.loadLong()
}

private fun sleep(nanos: Long, ptrTo32Bytes: Pointer, ptrTo8Bytes: Pointer, ptrToSubscription: Pointer) {
    //__wasi_timestamp_t timeout;
    (ptrToSubscription + 24).storeLong(nanos)
    val returnCode = wasiPollOneOff(
        ptrToSubscription = ptrToSubscription.address.toInt(),
        eventPtr = ptrTo32Bytes.address.toInt(),
        nsubscriptions = 1,
        resultPtr = ptrTo8Bytes.address.toInt()
    )
    check(returnCode == 0) { "poll_oneoff failed with the return code $returnCode" }
}

internal actual object DefaultExecutor : EventLoopImplBase() {
    override fun shutdown() {
        // don't do anything: on WASI, the event loop is the default executor, we can't shut it down
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle =
        scheduleInvokeOnTimeout(timeMillis, block)

    actual override fun enqueue(task: Runnable) {
        if (kotlin.wasm.internal.onExportedFunctionExit == null) {
            kotlin.wasm.internal.onExportedFunctionExit = ::runEventLoop
        }
        super.enqueue(task)
    }
}

internal actual abstract class EventLoopImplPlatform : EventLoop() {
    protected actual fun unpark() {
        // do nothing: in WASI, no external callbacks can be invoked while `poll_oneoff` is running,
        // so it is both impossible and unnecessary to unpark the event loop
    }

    protected actual fun reschedule(now: Long, delayedTask: EventLoopImplBase.DelayedTask) {
        // throw; on WASI, the event loop is the default executor, we can't shut it down or reschedule tasks
        // to anyone else
        throw UnsupportedOperationException("runBlocking event loop is not supported")
    }
}

internal actual inline fun platformAutoreleasePool(crossinline block: () -> Unit) = block()

internal fun runEventLoop() {
    withScopedMemoryAllocator { allocator ->
        val ptrToSubscription = initializeSubscriptionPtr(allocator)
        val ptrTo32Bytes = allocator.allocate(32)
        val ptrTo8Bytes = allocator.allocate(8)
        val eventLoop = DefaultExecutor
        eventLoop.incrementUseCount()
        try {
            while (true) {
                val parkNanos = eventLoop.processNextEvent()
                if (parkNanos == Long.MAX_VALUE) {
                    // no more events
                    break
                }
                if (parkNanos > 0) {
                    // sleep until the next event
                    sleep(
                        parkNanos,
                        ptrTo32Bytes = ptrTo32Bytes,
                        ptrTo8Bytes = ptrTo8Bytes,
                        ptrToSubscription = ptrToSubscription
                    )
                }
            }
        } finally { // paranoia
            eventLoop.decrementUseCount()
        }
    }
}

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

internal actual fun createDefaultDispatcher(): CoroutineDispatcher = DefaultExecutor
