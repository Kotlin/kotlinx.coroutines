/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.cinterop.*
import platform.posix.*
import kotlin.coroutines.*
import kotlin.system.*
import kotlin.native.concurrent.*

internal actual abstract class EventLoopImplPlatform : EventLoop() {

    private val current = Worker.current

    protected actual fun unpark() {
        current.execute(TransferMode.SAFE, {}) {} // send an empty task to unpark the waiting event loop
    }

    // TODO verify loop was shut down is an okay behaviour
    protected actual fun reschedule(now: Long, delayedTask: EventLoopImplBase.DelayedTask): Unit =
        loopWasShutDown()
}

internal class EventLoopImpl: EventLoopImplBase() {
    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle =
        scheduleInvokeOnTimeout(timeMillis, block)
}

internal actual fun createEventLoop(): EventLoop = EventLoopImpl()

internal actual fun nanoTime(): Long = getTimeNanos()
