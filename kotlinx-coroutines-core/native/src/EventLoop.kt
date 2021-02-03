/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.system.*

internal actual abstract class EventLoopImplPlatform: EventLoop() {
    protected actual fun unpark() { /* does nothing */ }
    protected actual fun reschedule(now: Long, delayedTask: EventLoopImplBase.DelayedTask): Unit =
        loopWasShutDown()
}

internal class EventLoopImpl: EventLoopImplBase() {
    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle =
        scheduleInvokeOnTimeout(timeMillis, block)
}

internal actual fun createEventLoop(): EventLoop = EventLoopImpl()

internal actual fun nanoTime(): Long = getTimeNanos()
