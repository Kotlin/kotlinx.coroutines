/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.native.concurrent.*

private fun takeEventLoop(): EventLoopImpl =
    ThreadLocalEventLoop.currentOrNull() as? EventLoopImpl ?:
        error("There is no event loop. Use runBlocking { ... } to start one.")

internal actual object DefaultExecutor : CoroutineDispatcher(), Delay {
    override fun dispatch(context: CoroutineContext, block: Runnable) =
        takeEventLoop().dispatch(context, block)
    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) =
        takeEventLoop().scheduleResumeAfterDelay(timeMillis, continuation)
    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle =
        takeEventLoop().invokeOnTimeout(timeMillis, block, context)

    actual fun enqueue(task: Runnable): Unit = loopWasShutDown()
}

internal fun loopWasShutDown(): Nothing = error("Cannot execute task because event loop was shut down")

internal actual fun createDefaultDispatcher(): CoroutineDispatcher =
    DefaultExecutor

@SharedImmutable
internal actual val DefaultDelay: Delay = DefaultExecutor

public actual fun CoroutineScope.newCoroutineContext(context: CoroutineContext): CoroutineContext {
    val combined = coroutineContext + context
    return if (combined !== DefaultExecutor && combined[ContinuationInterceptor] == null)
        combined + DefaultExecutor else combined
}

// No debugging facilities on native
internal actual inline fun <T> withCoroutineContext(context: CoroutineContext, countOrElement: Any?, block: () -> T): T = block()
internal actual inline fun <T> withContinuationContext(continuation: Continuation<*>, countOrElement: Any?, block: () -> T): T = block()
internal actual fun Continuation<*>.toDebugString(): String = toString()
internal actual val CoroutineContext.coroutineName: String? get() = null // not supported on native

internal actual class UndispatchedCoroutine<in T> actual constructor(
    context: CoroutineContext,
    uCont: Continuation<T>
) : ScopeCoroutine<T>(context, uCont) {
    override fun afterResume(state: Any?) = uCont.resumeWith(recoverResult(state, uCont))
}