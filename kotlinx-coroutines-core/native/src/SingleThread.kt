/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.native.concurrent.*

@ExperimentalCoroutinesApi
public actual fun newSingleThreadContext(name: String): SingleThreadDispatcher = SingleThreadDispatcherImpl(name)

/**
 * A coroutine dispatcher that is confined to a single thread.
 */
@ExperimentalCoroutinesApi
public actual abstract class SingleThreadDispatcher : CoroutineDispatcher() {
    public actual abstract fun close()
}

internal class SingleThreadDispatcherImpl(name: String) : SingleThreadDispatcher(), Delay {
    private val worker = Worker.start(name = name)

    override fun dispatch(context: CoroutineContext, block: Runnable) =
        worker.executeAfter(0L) { block.run() }

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        // TODO proper toMicros
        worker.executeAfter(timeMillis * 1000)
        { with(continuation) { resumeUndispatched(Unit) } }
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle {
        // No API to cancel on timeout
        worker.executeAfter(timeMillis * 1000) { block.run() }
        return NonDisposableHandle
    }

    override fun close() {
        worker.requestTermination().result // Note: calling "result" blocks
    }
}
