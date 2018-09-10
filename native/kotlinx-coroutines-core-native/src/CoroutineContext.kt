/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.*
import kotlinx.coroutines.experimental.timeunit.*

internal val currentEventLoop = ArrayList<BlockingEventLoop>()

private fun takeEventLoop(): BlockingEventLoop =
    currentEventLoop.firstOrNull() ?: error("There is no event loop. Use runBlocking { ... } to start one.")

internal object DefaultExecutor : CoroutineDispatcher(), Delay {
    override fun dispatch(context: CoroutineContext, block: Runnable) =
        takeEventLoop().dispatch(context, block)
    override fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>) =
        takeEventLoop().scheduleResumeAfterDelay(time, unit, continuation)
    override fun invokeOnTimeout(time: Long, unit: TimeUnit, block: Runnable): DisposableHandle =
        takeEventLoop().invokeOnTimeout(time, unit, block)

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

/**
 * This is the default [CoroutineDispatcher] that is used by all standard builders like
 * [launch], [async], etc if no dispatcher nor any other [ContinuationInterceptor] is specified in their context.
 */
public actual val DefaultDispatcher: CoroutineDispatcher = DefaultExecutor

internal actual val DefaultDelay: Delay = DefaultExecutor

public actual fun CoroutineScope.newCoroutineContext(context: CoroutineContext): CoroutineContext {
    val combined = coroutineContext + context
    return if (combined !== kotlinx.coroutines.experimental.DefaultDispatcher && combined[ContinuationInterceptor] == null)
        combined + kotlinx.coroutines.experimental.DefaultDispatcher else combined
}

// No debugging facilities on native
internal actual inline fun <T> withCoroutineContext(context: CoroutineContext, block: () -> T): T = block()
internal actual fun Continuation<*>.toDebugString(): String = toString()
internal actual val CoroutineContext.coroutineName: String? get() = null // not supported on native
