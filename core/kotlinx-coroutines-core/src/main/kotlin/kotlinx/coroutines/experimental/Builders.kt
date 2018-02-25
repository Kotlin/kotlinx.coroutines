/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// :todo: Remove after transition to Kotlin 1.2.30+
@file:Suppress("ACTUAL_FUNCTION_WITH_DEFAULT_ARGUMENTS")

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.intrinsics.*
import java.util.concurrent.locks.*
import kotlin.coroutines.experimental.*
import kotlin.coroutines.experimental.intrinsics.*

// --------------- basic coroutine builders ---------------

/**
 * Execute the given [block] in an unbounded executor.
 * If the current thread is a blocking one then the [block] is executed immediately,
 * otherwise the coroutine is suspended and the [block] is scheduled for execution on a different thread.
 */
public suspend fun <T> blocking(block: () -> T): T =
        if (!BlockingPool.isDispatchNeeded())
            // execute block undispatched
            block()
        else
            suspendCancellableCoroutine { continuation ->
                val runnable = object : Runnable {
                    @JvmField
                    @Volatile
                    var uncompletedContinuation: CancellableContinuation<T>? = continuation

                    override fun run() {
                        val res =
                                try {
                                    block()
                                } catch (exception: Throwable) {
                                    uncompletedContinuation?.resumeWithException(exception)
                                    return
                                }
                        uncompletedContinuation?.resume(res)
                    }
                }

                // execute block in blocking pool
                BlockingPool.execute(runnable)
                continuation.invokeOnCompletion { runnable.uncompletedContinuation = null }
            }

/**
 * Launches new coroutine without blocking current thread and returns a reference to the coroutine as a [Job].
 * The coroutine is cancelled when the resulting job is [cancelled][Job.cancel].
 *
 * The [context] for the new coroutine can be explicitly specified.
 * See [CoroutineDispatcher] for the standard context implementations that are provided by `kotlinx.coroutines`.
 * The [context][CoroutineScope.coroutineContext] of the parent coroutine from its [scope][CoroutineScope] may be used,
 * in which case the [Job] of the resulting coroutine is a child of the job of the parent coroutine.
 * The parent job may be also explicitly specified using [parent] parameter.
 *
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [DefaultDispatcher] is used.
 *
 * By default, the coroutine is immediately scheduled for execution.
 * Other options can be specified via `start` parameter. See [CoroutineStart] for details.
 * An optional [start] parameter can be set to [CoroutineStart.LAZY] to start coroutine _lazily_. In this case,
 * the coroutine [Job] is created in _new_ state. It can be explicitly started with [start][Job.start] function
 * and will be started implicitly on the first invocation of [join][Job.join].
 *
 * Uncaught exceptions in this coroutine cancel parent job in the context by default
 * (unless [CoroutineExceptionHandler] is explicitly specified), which means that when `launch` is used with
 * the context of another coroutine, then any uncaught exception leads to the cancellation of parent coroutine.
 *
 * See [newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
 *
 * @param context context of the coroutine. The default value is [DefaultDispatcher].
 * @param start coroutine start option. The default value is [CoroutineStart.DEFAULT].
 * @param parent explicitly specifies the parent job, overrides job from the [context] (if any).
 * @param block the coroutine code.
 */
public actual fun launch(
    context: CoroutineContext = DefaultDispatcher,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    parent: Job? = null,
    block: suspend CoroutineScope.() -> Unit
): Job {
    val newContext = newCoroutineContext(context, parent)
    val coroutine = if (start.isLazy)
        LazyStandaloneCoroutine(newContext, block) else
        StandaloneCoroutine(newContext, active = true)
    coroutine.start(start, coroutine, block)
    return coroutine
}

/** @suppress **Deprecated**: Binary compatibility */
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun launch(
    context: CoroutineContext = DefaultDispatcher,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> Unit
): Job =
    launch(context, start, block = block)

/**
 * @suppress **Deprecated**: Use `start = CoroutineStart.XXX` parameter
 */
@Deprecated(message = "Use `start = CoroutineStart.XXX` parameter",
    replaceWith = ReplaceWith("launch(context, if (start) CoroutineStart.DEFAULT else CoroutineStart.LAZY, block)"))
public fun launch(context: CoroutineContext, start: Boolean, block: suspend CoroutineScope.() -> Unit): Job =
    launch(context, if (start) CoroutineStart.DEFAULT else CoroutineStart.LAZY, block = block)

/**
 * Calls the specified suspending block with a given coroutine context, suspends until it completes, and returns
 * the result.
 *
 * This function immediately applies dispatcher from the new context, shifting execution of the block into the
 * different thread inside the block, and back when it completes.
 * The specified [context] is added onto the current coroutine context for the execution of the block.
 *
 * An optional `start` parameter is used only if the specified `context` uses a different [CoroutineDispatcher] than
 * a current one, otherwise it is ignored.
 * By default, the coroutine is immediately scheduled for execution and can be cancelled
 * while it is waiting to be executed and it can be cancelled while the result is scheduled
 * to be processed by the invoker context.
 * Other options can be specified via `start` parameter. See [CoroutineStart] for details.
 * A value of [CoroutineStart.LAZY] is not supported and produces [IllegalArgumentException].
 */
public actual suspend fun <T> withContext(
    context: CoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend () -> T
): T = suspendCoroutineOrReturn sc@ { cont ->
    val oldContext = cont.context
    // fast path #1 if there is no change in the actual context:
    if (context === oldContext || context is CoroutineContext.Element && oldContext[context.key] === context)
        return@sc block.startCoroutineUninterceptedOrReturn(cont)
    // compute new context
    val newContext = oldContext + context
    // fast path #2 if the result is actually the same
    if (newContext === oldContext)
        return@sc block.startCoroutineUninterceptedOrReturn(cont)
    // fast path #3 if the new dispatcher is the same as the old one.
    // `equals` is used by design (see equals implementation is wrapper context like ExecutorCoroutineDispatcher)
    if (newContext[ContinuationInterceptor] == oldContext[ContinuationInterceptor]) {
        val newContinuation = RunContinuationDirect(newContext, cont)
        return@sc block.startCoroutineUninterceptedOrReturn(newContinuation)
    }
    // slowest path otherwise -- use new interceptor, sync to its result via a full-blown instance of RunCompletion
    require(!start.isLazy) { "$start start is not supported" }
    val completion = RunCompletion(
        context = newContext,
        delegate = cont,
        resumeMode = if (start == CoroutineStart.ATOMIC) MODE_ATOMIC_DEFAULT else MODE_CANCELLABLE)
    completion.initParentJobInternal(newContext[Job]) // attach to job
    @Suppress("DEPRECATION")
    start(block, completion)
    completion.getResult()
}

/** @suppress **Deprecated**: Renamed to [withContext]. */
@Deprecated(message = "Renamed to `withContext`", level=DeprecationLevel.WARNING,
    replaceWith = ReplaceWith("withContext(context, start, block)"))
public suspend fun <T> run(
    context: CoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend () -> T
): T =
    withContext(context, start, block)

/** @suppress **Deprecated** */
@Deprecated(message = "It is here for binary compatibility only", level=DeprecationLevel.HIDDEN)
public suspend fun <T> run(context: CoroutineContext, block: suspend () -> T): T =
    withContext(context, start = CoroutineStart.ATOMIC, block = block)

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
@Throws(InterruptedException::class)
public fun <T> runBlocking(context: CoroutineContext = EmptyCoroutineContext, block: suspend CoroutineScope.() -> T): T {
    val currentThread = Thread.currentThread()
    val contextInterceptor = context[ContinuationInterceptor]
    val privateEventLoop = contextInterceptor == null // create private event loop if no dispatcher is specified
    val eventLoop = if (privateEventLoop) BlockingEventLoop(currentThread) else contextInterceptor as? EventLoop
    val newContext = newCoroutineContext(
        if (privateEventLoop) context + (eventLoop as ContinuationInterceptor) else context
    )
    val coroutine = BlockingCoroutine<T>(newContext, currentThread, eventLoop, privateEventLoop)
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
    return coroutine.joinBlocking()
}

// --------------- implementation ---------------

private open class StandaloneCoroutine(
    private val parentContext: CoroutineContext,
    active: Boolean
) : AbstractCoroutine<Unit>(parentContext, active) {
    override fun hasOnFinishingHandler(update: Any?) = update is CompletedExceptionally
    override fun onFinishingInternal(update: Any?) {
        // note the use of the parent's job context below!
        if (update is CompletedExceptionally) handleCoroutineException(parentContext, update.exception)
    }
}

private class LazyStandaloneCoroutine(
    parentContext: CoroutineContext,
    private val block: suspend CoroutineScope.() -> Unit
) : StandaloneCoroutine(parentContext, active = false) {
    override fun onStart() {
        block.startCoroutineCancellable(this, this)
    }
}

private class RunContinuationDirect<in T>(
    override val context: CoroutineContext,
    continuation: Continuation<T>
) : Continuation<T> by continuation


@Suppress("UNCHECKED_CAST")
private class RunCompletion<in T>(
    override val context: CoroutineContext,
    delegate: Continuation<T>,
    resumeMode: Int
) : AbstractContinuation<T>(delegate, resumeMode)

private class BlockingCoroutine<T>(
    parentContext: CoroutineContext,
    private val blockedThread: Thread,
    private val eventLoop: EventLoop?,
    private val privateEventLoop: Boolean
) : AbstractCoroutine<T>(parentContext, true) {
    init {
        if (privateEventLoop) require(eventLoop is BlockingEventLoop)
    }

    override fun onCancellationInternal(exceptionally: CompletedExceptionally?) {
        // wake up blocked thread
        if (Thread.currentThread() != blockedThread)
            LockSupport.unpark(blockedThread)
    }

    @Suppress("UNCHECKED_CAST")
    fun joinBlocking(): T {
        timeSource.registerTimeLoopThread()
        while (true) {
            if (Thread.interrupted()) throw InterruptedException().also { cancel(it) }
            val parkNanos = eventLoop?.processNextEvent() ?: Long.MAX_VALUE
            // note: process next even may loose unpark flag, so check if completed before parking
            if (isCompleted) break
            timeSource.parkNanos(this, parkNanos)
        }
        // process queued events (that could have been added after last processNextEvent and before cancel
        if (privateEventLoop) (eventLoop as BlockingEventLoop).apply {
            // We exit the "while" loop above when this coroutine's state "isCompleted",
            // Here we should signal that BlockingEventLoop should not accept any more tasks
            isCompleted = true
            shutdown()
        }
        timeSource.unregisterTimeLoopThread()
        // now return result
        val state = this.state
        (state as? CompletedExceptionally)?.let { throw it.exception }
        return state as T
    }
}
