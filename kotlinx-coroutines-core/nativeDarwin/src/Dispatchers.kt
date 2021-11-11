/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.cinterop.*
import kotlinx.coroutines.internal.*
import platform.CoreFoundation.*
import platform.darwin.*
import kotlin.coroutines.*
import kotlin.native.concurrent.*
import kotlin.native.internal.NativePtr

internal fun isMainThread(): Boolean = CFRunLoopGetCurrent() == CFRunLoopGetMain()

internal actual fun createMainDispatcher(default: CoroutineDispatcher): MainCoroutineDispatcher =
    if (multithreadingSupported) DarwinMainDispatcher(false) else OldMainDispatcher(Dispatchers.Default)

internal actual fun createDefaultDispatcher(): CoroutineDispatcher = DarwinGlobalQueueDispatcher

private object DarwinGlobalQueueDispatcher : CoroutineDispatcher() {
    override fun dispatch(context: CoroutineContext, block: Runnable) {
        autoreleasepool {
            dispatch_async(dispatch_get_global_queue(DISPATCH_QUEUE_PRIORITY_DEFAULT.convert(), 0)) {
                block.run()
            }
        }
    }
}

private class DarwinMainDispatcher(
    private val invokeImmediately: Boolean
) : MainCoroutineDispatcher(), Delay {
    
    override val immediate: MainCoroutineDispatcher =
        if (invokeImmediately) this else DarwinMainDispatcher(true)

    override fun isDispatchNeeded(context: CoroutineContext): Boolean = !(invokeImmediately && isMainThread())

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        autoreleasepool {
            dispatch_async(dispatch_get_main_queue()) {
                block.run()
            }
        }
    }
    
    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val timer = Timer()
        val timerBlock: TimerBlock = {
            timer.dispose()
            continuation.resume(Unit)
        }
        timer.start(timeMillis, timerBlock)
        continuation.disposeOnCancellation(timer)
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle {
        val timer = Timer()
        val timerBlock: TimerBlock = {
            timer.dispose()
            block.run()
        }
        timer.start(timeMillis, timerBlock)
        return timer
    }

    override fun toString(): String =
        "MainDispatcher${ if(invokeImmediately) "[immediate]" else "" }"
}

private typealias TimerBlock = (CFRunLoopTimerRef?) -> Unit

private val TIMER_NEW = NativePtr.NULL
private val TIMER_DISPOSED = NativePtr.NULL.plus(1)

private class Timer : DisposableHandle {
    private val ref = AtomicNativePtr(TIMER_NEW)

    fun start(timeMillis: Long, timerBlock: TimerBlock) {
        val fireDate = CFAbsoluteTimeGetCurrent() + timeMillis / 1000.0
        val timer = CFRunLoopTimerCreateWithHandler(null, fireDate, 0.0, 0u, 0, timerBlock)
        CFRunLoopAddTimer(CFRunLoopGetMain(), timer, kCFRunLoopCommonModes)
        if (!ref.compareAndSet(TIMER_NEW, timer.rawValue)) {
            // dispose was already called concurrently
            release(timer)
        }
    }

    override fun dispose() {
        while (true) {
            val ptr = ref.value
            if (ptr == TIMER_DISPOSED) return
            if (ref.compareAndSet(ptr, TIMER_DISPOSED)) {
                if (ptr != TIMER_NEW) release(interpretCPointer(ptr))
                return
            }
        }
    }

    private fun release(timer: CFRunLoopTimerRef?) {
        CFRunLoopRemoveTimer(CFRunLoopGetMain(), timer, kCFRunLoopCommonModes)
        CFRelease(timer)
    }
}

internal actual inline fun platformAutoreleasePool(crossinline block: () -> Unit): Unit = autoreleasepool { block() }
