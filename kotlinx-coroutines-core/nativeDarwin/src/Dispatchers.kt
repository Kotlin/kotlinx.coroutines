/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.cinterop.*
import platform.CoreFoundation.*
import platform.darwin.*
import kotlin.coroutines.*
import kotlin.native.concurrent.*
import kotlin.native.internal.NativePtr

internal fun isMainThread(): Boolean = CFRunLoopGetCurrent() == CFRunLoopGetMain()

internal actual fun createMainDispatcher(default: CoroutineDispatcher): MainCoroutineDispatcher =
    DarwinMainDispatcher(false)

@Suppress("EXPERIMENTAL_UNSIGNED_LITERALS")
private class DarwinMainDispatcher(
    private val invokeImmediately: Boolean
) : MainCoroutineDispatcher(), Delay, ThreadBoundInterceptor {
    override val thread
        get() = mainThread
    
    override val immediate: MainCoroutineDispatcher =
        if (invokeImmediately) this else DarwinMainDispatcher(true)

    init { freeze() }

    override fun isDispatchNeeded(context: CoroutineContext): Boolean = !(invokeImmediately && isMainThread())

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        dispatch_async(dispatch_get_main_queue()) {
            block.run()
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

internal typealias TimerBlock = (CFRunLoopTimerRef?) -> Unit

@SharedImmutable
private val TIMER_NEW = NativePtr.NULL

@SharedImmutable
private val TIMER_DISPOSED = NativePtr.NULL.plus(1)

private class Timer : DisposableHandle {
    private val ref = AtomicNativePtr(TIMER_NEW)

    init { freeze() }

    fun start(timeMillis: Long, timerBlock: TimerBlock) {
        val fireDate = CFAbsoluteTimeGetCurrent() + timeMillis / 1000.0
        @Suppress("EXPERIMENTAL_UNSIGNED_LITERALS")
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
