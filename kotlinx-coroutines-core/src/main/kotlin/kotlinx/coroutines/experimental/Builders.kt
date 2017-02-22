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
 * An optional [start] parameter can be set to `false` to start coroutine _lazily_. When `start = false`,
 * the coroutine [Job] is created in _new_ state. It can be explicitly started with [start][Job.start] function
 * and will be started implicitly on the first invocation of [join][Job.join].
 *
 * Uncaught exceptions in this coroutine cancel parent job in the context by default
 * (unless [CoroutineExceptionHandler] is explicitly specified), which means that when `launch` is used with
 * the context of another coroutine, then any uncaught exception leads to the cancellation of parent coroutine.
 *
 * See [newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
 */
fun launch(context: CoroutineContext, start: Boolean = true, block: suspend CoroutineScope.() -> Unit): Job {
    val newContext = newCoroutineContext(context)
    val coroutine = if (start)
        StandaloneCoroutine(newContext, active = true) else
        LazyStandaloneCoroutine(newContext, block)
    coroutine.initParentJob(context[Job])
    if (start) block.startCoroutine(coroutine, coroutine)
    return coroutine
}

/**
 * Calls the specified suspending block with a given coroutine context, suspends until it completes, and returns
 * the result.
 *
 * This function immediately applies dispatcher from the new context, shifting execution of the block into the
 * different thread inside the block, and back when it completes.
 * The specified [context] is added onto the current coroutine context for the execution of the block.
 */
public suspend fun <T> run(context: CoroutineContext, block: suspend CoroutineScope.() -> T): T =
    suspendCoroutine { cont ->
        // new don't invoke `newCoroutineContext`, but consider this being the same coroutine in the new context
        InnerCoroutine(cont.context + context, cont).also { block.startCoroutine(it, it) }
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
    val privateEventLoop = if (context[ContinuationInterceptor] == null) EventLoopImpl(currentThread) else null
    val newContext = newCoroutineContext(context + (privateEventLoop ?: EmptyCoroutineContext))
    val coroutine = BlockingCoroutine<T>(newContext, currentThread, privateEventLoop != null)
    coroutine.initParentJob(context[Job])
    privateEventLoop?.initParentJob(coroutine)
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
    val block: suspend CoroutineScope.() -> Unit
) : StandaloneCoroutine(parentContext, active = false) {
    override fun onStart() {
        block.startCoroutine(this, this)
    }
}

private class InnerCoroutine<in T>(
    override val context: CoroutineContext,
    continuation: Continuation<T>
) : Continuation<T> by continuation, CoroutineScope {
    override val isActive: Boolean = context[Job]?.isActive ?: true
}

private class BlockingCoroutine<T>(
    override val parentContext: CoroutineContext,
    val blockedThread: Thread,
    val hasPrivateEventLoop: Boolean
) : AbstractCoroutine<T>(active = true) {
    val eventLoop: EventLoop? = parentContext[ContinuationInterceptor] as? EventLoop

    override fun afterCompletion(state: Any?, mode: Int) {
        if (Thread.currentThread() != blockedThread)
            LockSupport.unpark(blockedThread)
    }

    @Suppress("UNCHECKED_CAST")
    fun joinBlocking(): T {
        while (isActive) {
            if (Thread.interrupted()) throw InterruptedException().also { cancel(it) }
            if (eventLoop == null || !eventLoop.processNextEvent())
                LockSupport.park(this)
        }
        // process remaining events (that could have been added after last processNextEvent and before cancel
        if (hasPrivateEventLoop) {
            while (eventLoop!!.processNextEvent()) { /* just spin */ }
        }
        // now return result
        val state = this.state
        (state as? CompletedExceptionally)?.let { throw it.exception }
        return state as T
    }
}
