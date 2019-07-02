/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

internal actual abstract class EventLoopImplPlatform: EventLoop() {
    protected abstract val thread: Thread

    protected actual fun unpark() {
        val thread = thread // atomic read
        if (Thread.currentThread() !== thread)
            unpark(thread)
    }
}

internal class BlockingEventLoop(
    override val thread: Thread
) : EventLoopImplBase()

internal actual fun createEventLoop(): EventLoop = BlockingEventLoop(Thread.currentThread())

/**
 * Processes next event in the current thread's event loop.
 *
 * The result of this function is to be interpreted like this:
 * * `<= 0` -- there are potentially more events for immediate processing;
 * * `> 0` -- a number of nanoseconds to wait for the next scheduled event;
 * * [Long.MAX_VALUE] -- no more events or no thread-local event loop.
 *
 * Sample usage of this function:
 *
 * ```
 * while (waitingCondition) {
 *     val time = processNextEventInCurrentThread()
 *     LockSupport.parkNanos(time)
 * }
 * ```
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public fun processNextEventInCurrentThread(): Long =
    ThreadLocalEventLoop.currentOrNull()?.processNextEvent() ?: Long.MAX_VALUE