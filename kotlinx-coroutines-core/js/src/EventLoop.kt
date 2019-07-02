/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*

internal actual fun createEventLoop(): EventLoop = UnconfinedEventLoop()

internal actual fun nanoTime(): Long = unsupported()

internal class UnconfinedEventLoop : EventLoop() {
    override fun dispatch(context: CoroutineContext, block: Runnable): Unit = unsupported()
}

internal actual abstract class EventLoopImplPlatform : EventLoop() {
    protected actual fun unpark(): Unit = unsupported()
}

internal actual object DefaultExecutor {
    public actual fun enqueue(task: Runnable): Unit = unsupported()
    public actual fun schedule(delayedTask: EventLoopImplBase.DelayedTask): Unit = unsupported()
}

private fun unsupported(): Nothing =
    throw UnsupportedOperationException("runBlocking event loop is not supported")
