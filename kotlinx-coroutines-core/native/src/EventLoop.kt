/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.system.*

internal actual abstract class EventLoopImplPlatform: EventLoop() {
    protected actual fun unpark() { /* does nothing */ }
}

internal class EventLoopImpl: EventLoopImplBase() {
    override fun invokeOnTimeout(timeMillis: Long, block: Runnable): DisposableHandle =
        DelayedRunnableTask(timeMillis, block).also { schedule(it) }
}

internal actual fun createEventLoop(): EventLoop = EventLoopImpl()

internal actual fun nanoTime(): Long = getTimeNanos()