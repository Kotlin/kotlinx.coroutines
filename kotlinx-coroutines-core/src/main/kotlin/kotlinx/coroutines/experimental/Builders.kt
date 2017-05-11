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

package kotlinx.coroutines.experimental

import java.util.concurrent.locks.LockSupport
import kotlin.coroutines.experimental.*
import kotlin.coroutines.experimental.intrinsics.startCoroutineUninterceptedOrReturn
import kotlin.coroutines.experimental.intrinsics.suspendCoroutineOrReturn

// --------------- basic coroutine builders ---------------

/**
 * Launches new coroutine without blocking current thread and returns a reference to the coroutine as a [Job].
 * The coroutine is cancelled when the resulting job is [cancelled][Job.cancel].
 *
 * The [context] for the new coroutine must be explicitly specified.
 * See [CoroutineDispatcher] for the standard [context] implementations that are provided by `kotlinx.coroutines`.
 * The [context][CoroutineScope.context] of the parent coroutine from its [scope][CoroutineScope] may be used,
 * in which case the [Job] of the resulting coroutine is a child of the job of the parent coroutine.
 *
 * By default, the coroutine is immediately started.
 * An optional [start] parameter can be set to [CoroutineStart.LAZY] to start coroutine _lazily_. In this case,
 * the coroutine [Job] is created in _new_ state. It can be explicitly started with [start][Job.start] function
 * and will be started implicitly on the first invocation of [join][Job.join].
 *
 * Uncaught exceptions in this coroutine cancel parent job in the context by default
 * (unless [CoroutineExceptionHandler] is explicitly specified), which means that when `launch` is used with
 * the context of another coroutine, then any uncaught exception leads to the cancellation of parent coroutine.
 *
 * See [newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.

 * @param context context of the coroutine
 * @param start coroutine start option
 * @param block the coroutine code
 */
public fun launch(
    context: CoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> Unit
): Job {
    val newContext = newCoroutineContext(context)
    val coroutine = if (start.isLazy)
        LazyStandaloneCoroutine(newContext, block) else
        StandaloneCoroutine(newContext, active = true)
    coroutine.initParentJob(context[Job])
    start(block, coroutine, coroutine)
    return coroutine
}

/**
 * @suppress **Deprecated**: Use `start = CoroutineStart.XXX` parameter
 */
@Deprecated(message = "Use `start = CoroutineStart.XXX` parameter",
    replaceWith = ReplaceWith("launch(context, if (start) CoroutineStart.DEFAULT else CoroutineStart.LAZY, block)"))
public fun launch(context: CoroutineContext, start: Boolean, block: suspend CoroutineScope.() -> Unit): Job =
    launch(context, if (start) CoroutineStart.DEFAULT else CoroutineStart.LAZY, block)

/**
 * Calls the specified suspending block with a given coroutine context, suspends until it completes, and returns
 * the result.
 *
 * This function immediately applies dispatcher from the new context, shifting execution of the block into the
 * different thread inside the block, and back when it completes.
 * The specified [context] is added onto the current coroutine context for the execution of the block.
 */
public suspend fun <T> run(context: CoroutineContext, block: suspend () -> T): T =
    suspendCoroutineOrReturn sc@ { cont ->
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
        // slowest path otherwise -- use new interceptor, sync to its result via a
        // full-blown instance of CancellableContinuation
        val newContinuation = RunContinuationCoroutine(newContext, cont)
        newContinuation.initCancellability()
        block.startCoroutine(newContinuation)
        newContinuation.getResult()
    }

/**
 * Runs new coroutine and **blocks** current thread _interruptibly_ until its completion.
 * This function should not be used from coroutine. It is designed to bridge regular blocking code
 * to libraries that are written in suspending style, to be used in `main` functions and in tests.
 *
 * The default [CoroutineDispatcher] for this builder in an implementation of [EventLoop] that processes continuations
 * in this blocked thread until the completion of this coroutine.
 * See [CoroutineDispatcher] for the other implementations that are provided by `kotlinx.coroutines`.
 *
 * If this blocked thread is interrupted (see [Thread.interrupt]), then the coroutine job is cancelled and
 * this `runBlocking` invocation throws [InterruptedException].
 *
 * See [newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
 */
@Throws(InterruptedException::class)
public fun <T> runBlocking(context: CoroutineContext = EmptyCoroutineContext, block: suspend CoroutineScope.() -> T): T {
    val currentThread = Thread.currentThread()
    val eventLoop = if (context[ContinuationInterceptor] == null) EventLoopImpl(currentThread) else null
    val newContext = newCoroutineContext(context + (eventLoop ?: EmptyCoroutineContext))
    val coroutine = BlockingCoroutine<T>(newContext, currentThread, privateEventLoop = eventLoop != null)
    coroutine.initParentJob(context[Job])
    eventLoop?.initParentJob(coroutine)
    block.startCoroutine(coroutine, coroutine)
    return coroutine.joinBlocking()
}

// --------------- implementation ---------------

private open class StandaloneCoroutine(
    override val parentContext: CoroutineContext,
    active: Boolean
) : AbstractCoroutine<Unit>(active) {
    override fun afterCompletion(state: Any?, mode: Int) {
        // note the use of the parent's job context below!
        if (state is CompletedExceptionally) handleCoroutineException(parentContext, state.exception)
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

private class RunContinuationCoroutine<in T>(
    override val parentContext: CoroutineContext,
    continuation: Continuation<T>
) : CancellableContinuationImpl<T>(continuation, defaultResumeMode = MODE_CANCELLABLE, active = true)

private class BlockingCoroutine<T>(
    override val parentContext: CoroutineContext,
    private val blockedThread: Thread,
    private val privateEventLoop: Boolean
) : AbstractCoroutine<T>(active = true) {
    val eventLoop: EventLoop? = parentContext[ContinuationInterceptor] as? EventLoop

    init {
        if (privateEventLoop) require(eventLoop is EventLoopImpl)
    }

    override fun afterCompletion(state: Any?, mode: Int) {
        if (Thread.currentThread() != blockedThread)
            LockSupport.unpark(blockedThread)
    }

    @Suppress("UNCHECKED_CAST")
    fun joinBlocking(): T {
        while (true) {
            if (Thread.interrupted()) throw InterruptedException().also { cancel(it) }
            val parkNanos = eventLoop?.processNextEvent() ?: Long.MAX_VALUE
            // note: process next even may look unpark flag, so check !isActive before parking
            if (!isActive) break
            LockSupport.parkNanos(this, parkNanos)
        }
        // process queued events (that could have been added after last processNextEvent and before cancel
        if (privateEventLoop) (eventLoop as EventLoopImpl).shutdown()
        // now return result
        val state = this.state
        (state as? CompletedExceptionally)?.let { throw it.exception }
        return state as T
    }
}
