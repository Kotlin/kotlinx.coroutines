/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlinx.coroutines.internal.*

@ThreadLocal
internal val currentEventLoop = ArrayList<BlockingEventLoop>()

private fun takeEventLoop(): BlockingEventLoop =
    currentEventLoop.firstOrNull() ?: error("There is no event loop. Use runBlocking { ... } to start one.")

internal object DefaultExecutor : CoroutineDispatcher(), Delay {
    override fun dispatch(context: CoroutineContext, block: Runnable) =
        takeEventLoop().dispatch(context, block)
    override fun scheduleResumeAfterDelay(time: Long, continuation: CancellableContinuation<Unit>) =
        takeEventLoop().scheduleResumeAfterDelay(time, continuation)
    override fun invokeOnTimeout(time: Long, block: Runnable): DisposableHandle =
        takeEventLoop().invokeOnTimeout(time, block)

    fun execute(task: Runnable) {
        error("Cannot execute task because event loop was shut down")
    }

    fun schedule(delayedTask: EventLoopBase.DelayedTask) {
        error("Cannot schedule task because event loop was shut down")
    }

    fun removeDelayedImpl(delayedTask: EventLoopBase.DelayedTask) {
        error("Cannot happen")
    }
}

internal actual fun createDefaultDispatcher(): CoroutineDispatcher =
    DefaultExecutor

internal actual val DefaultDelay: Delay = DefaultExecutor

public actual fun CoroutineScope.newCoroutineContext(context: CoroutineContext): CoroutineContext {
    val combined = coroutineContext + context
    return if (combined !== kotlinx.coroutines.DefaultExecutor && combined[ContinuationInterceptor] == null)
        combined + kotlinx.coroutines.DefaultExecutor else combined
}

// No debugging facilities on native
internal actual inline fun <T> withCoroutineContext(context: CoroutineContext, countOrElement: Any?, block: () -> T): T = block()
internal actual fun Continuation<*>.toDebugString(): String = toString()
internal actual val CoroutineContext.coroutineName: String? get() = null // not supported on native
