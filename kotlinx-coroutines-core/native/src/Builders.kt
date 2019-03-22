/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*

/**
 * Runs new coroutine and **blocks** current thread _interruptibly_ until its completion.
 * This function should not be used from coroutine. It is designed to bridge regular blocking code
 * to libraries that are written in suspending style, to be used in `main` functions and in tests.
 *
 * The default [CoroutineDispatcher] for this builder in an implementation of [EventLoop] that processes continuations
 * in this blocked thread until the completion of this coroutine.
 * See [CoroutineDispatcher] for the other implementations that are provided by `kotlinx.coroutines`.
 *
 * When [CoroutineDispatcher] is explicitly specified in the [context], then the new coroutine runs in the context of
 * the specified dispatcher while the current thread is blocked. If the specified dispatcher implements [EventLoop]
 * interface and this `runBlocking` invocation is performed from inside of the this event loop's thread, then
 * this event loop is processed using its [processNextEvent][EventLoop.processNextEvent] method until coroutine completes.
 *
 * If this blocked thread is interrupted (see [Thread.interrupt]), then the coroutine job is cancelled and
 * this `runBlocking` invocation throws [InterruptedException].
 *
 * See [newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
 *
 * @param context context of the coroutine. The default value is an implementation of [EventLoop].
 * @param block the coroutine code.
 */
public fun <T> runBlocking(context: CoroutineContext = EmptyCoroutineContext, block: suspend CoroutineScope.() -> T): T {
    val contextInterceptor = context[ContinuationInterceptor]
    val eventLoop: EventLoop?
    var newContext: CoroutineContext = context // todo: kludge for data flow analysis error
    if (contextInterceptor == null) {
        // create or use private event loop if no dispatcher is specified
        eventLoop = ThreadLocalEventLoop.eventLoop
        newContext = GlobalScope.newCoroutineContext(context + eventLoop)
    } else {
        // See if context's interceptor is an event loop that we shall use (to support TestContext)
        // or take an existing thread-local event loop if present to avoid blocking it (but don't create one)
        eventLoop = (contextInterceptor as? EventLoop)?.takeIf { it.shouldBeProcessedFromContext() }
            ?: ThreadLocalEventLoop.currentOrNull()
        newContext = GlobalScope.newCoroutineContext(context)
    }
    val coroutine = BlockingCoroutine<T>(newContext, eventLoop)
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
    return coroutine.joinBlocking()
}

private class BlockingCoroutine<T>(
    parentContext: CoroutineContext,
    private val eventLoop: EventLoop?
) : AbstractCoroutine<T>(parentContext, true) {
    override val cancelsParent: Boolean
        get() = false // it throws exception to parent instead of cancelling it

    @Suppress("UNCHECKED_CAST")
    fun joinBlocking(): T {
        try {
            eventLoop?.incrementUseCount()
            while (true) {
                val parkNanos = eventLoop?.processNextEvent() ?: Long.MAX_VALUE
                // note: process next even may loose unpark flag, so check if completed before parking
                if (isCompleted) break
                // todo: LockSupport.parkNanos(this, parkNanos)
            }
        } finally { // paranoia
            eventLoop?.decrementUseCount()
        }
        // now return result
        val state = this.state
        (state as? CompletedExceptionally)?.let { throw it.cause }
        return state as T
    }
}
