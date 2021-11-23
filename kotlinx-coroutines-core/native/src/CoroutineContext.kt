/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.native.concurrent.*

internal actual object DefaultExecutor : CoroutineDispatcher(), Delay {

    private val delegate = WorkerDispatcher(name = "DefaultExecutor")

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        checkState()
        delegate.dispatch(context, block)
    }

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        checkState()
        delegate.scheduleResumeAfterDelay(timeMillis, continuation)
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle {
        checkState()
        return delegate.invokeOnTimeout(timeMillis, block, context)
    }

    actual fun enqueue(task: Runnable): Unit {
        checkState()
        delegate.dispatch(EmptyCoroutineContext, task)
    }

    private fun checkState() {
        if (multithreadingSupported) return
        error("DefaultExecutor should never be invoked in K/N with disabled new memory model. The top-most 'runBlocking' event loop has been shutdown")
    }
}

internal expect fun createDefaultDispatcher(): CoroutineDispatcher

@SharedImmutable
internal actual val DefaultDelay: Delay = if (multithreadingSupported) DefaultExecutor else OldDefaultExecutor

public actual fun CoroutineScope.newCoroutineContext(context: CoroutineContext): CoroutineContext {
    val combined = coroutineContext + context
    return if (combined !== DefaultDelay && combined[ContinuationInterceptor] == null)
        combined + (DefaultDelay as CoroutineContext.Element) else combined
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
