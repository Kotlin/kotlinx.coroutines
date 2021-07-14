/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.native.concurrent.*

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
public actual fun <T> runBlocking(context: CoroutineContext, block: suspend CoroutineScope.() -> T): T {
    val contextInterceptor = context[ContinuationInterceptor]
    val eventLoop: EventLoop?
    var newContext: CoroutineContext = context // todo: kludge for data flow analysis error
    if (contextInterceptor == null) {
        // create or use private event loop if no dispatcher is specified
        eventLoop = ThreadLocalEventLoop.eventLoop
        newContext = GlobalScope.newCoroutineContext(context + eventLoop.asShareable())
    } else {
        // See if context's interceptor is an event loop that we shall use (to support TestContext)
        // or take an existing thread-local event loop if present to avoid blocking it (but don't create one)
        eventLoop = (contextInterceptor as? EventLoop)?.takeIf { it.shouldBeProcessedFromContext() }
            ?: ThreadLocalEventLoop.currentOrNull()
        newContext = GlobalScope.newCoroutineContext(context)
    }
    val coroutine = BlockingCoroutine<T>(newContext)
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
    return coroutine.joinBlocking(eventLoop)
}

private class BlockingCoroutine<T>(
    parentContext: CoroutineContext
) : AbstractCoroutine<T>(parentContext, true, true) {
    override val isScopedCoroutine: Boolean get() = true
    private val worker = Worker.current

    override fun afterCompletion(state: Any?) {
        // wake up blocked worker
        if (Worker.current != worker)
            worker.execute(TransferMode.SAFE, {}) {} // send an empty task
    }

    @Suppress("UNCHECKED_CAST")
    fun joinBlocking(eventLoop: EventLoop?): T {
        runEventLoop(eventLoop) { isCompleted }
        // now return result
        val state = state.unboxState()
        (state as? CompletedExceptionally)?.let { throw it.cause }
        return state as T
    }
}

internal fun runEventLoop(eventLoop: EventLoop?, isCompleted: () -> Boolean) {
    try {
        eventLoop?.incrementUseCount()
        val thread = currentThread()
        while (!isCompleted()) {
            val parkNanos = eventLoop?.processNextEvent() ?: Long.MAX_VALUE
            if (isCompleted()) break
            thread.parkNanos(parkNanos)
        }
    } finally { // paranoia
        eventLoop?.decrementUseCount()
    }
}

// --------------- Kotlin/Native specialization hooks ---------------

// just start
internal actual fun <T, R> startCoroutine(
    start: CoroutineStart,
    receiver: R,
    completion: Continuation<T>,
    onCancellation: ((cause: Throwable) -> Unit)?,
    block: suspend R.() -> T
) =
    startCoroutine(start, receiver, completion, onCancellation, block) {}

// initParentJob + startCoroutine
internal actual fun <T, R> startAbstractCoroutine(
    start: CoroutineStart,
    receiver: R,
    coroutine: AbstractCoroutine<T>,

    block: suspend R.() -> T
) {
    // See https://github.com/Kotlin/kotlinx.coroutines/issues/2064
    // We shall do initParentJob only after freezing the block
    startCoroutine(start, receiver, coroutine, null, block) {
        coroutine.initParentJob(coroutine.parentContext[Job])
    }
}

private fun <T, R> startCoroutine(
    start: CoroutineStart,
    receiver: R,
    completion: Continuation<T>,
    onCancellation: ((cause: Throwable) -> Unit)?,
    block: suspend R.() -> T,
    initParentJobIfNeeded: () -> Unit
) {
    val curThread = currentThread()
    val newThread = completion.context[ContinuationInterceptor].thread()
    if (newThread != curThread) {
        check(start != CoroutineStart.UNDISPATCHED) {
            "Cannot start an undispatched coroutine in another thread $newThread from current $curThread"
        }
        block.freeze() // freeze the block, safely get FreezingException if it cannot be frozen
        initParentJobIfNeeded() // only initParentJob here if needed
        if (start != CoroutineStart.LAZY) {
            newThread.execute {
                startCoroutineImpl(start, receiver, completion, onCancellation, block)
            }
        }
        return
    }
    initParentJobIfNeeded()
    startCoroutineImpl(start, receiver, completion, onCancellation, block)
}

private fun ContinuationInterceptor?.thread(): Thread = when (this) {
    null -> Dispatchers.Default.thread()
    is ThreadBoundInterceptor -> thread
    else -> currentThread() // fallback
}

internal actual fun <T, R> saveLazyCoroutine(
    coroutine: AbstractCoroutine<T>,
    receiver: R,
    block: suspend R.() -> T
): Any =
    block

@Suppress("NOTHING_TO_INLINE", "UNCHECKED_CAST") // Save an entry on call stack
internal actual fun <T, R> startLazyCoroutine(
    saved: Any,
    coroutine: AbstractCoroutine<T>,
    receiver: R
) =
    startCoroutine(CoroutineStart.DEFAULT, receiver, coroutine, null, saved as suspend R.() -> T)
