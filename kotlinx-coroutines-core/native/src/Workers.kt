/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlin.coroutines.*
import kotlin.native.concurrent.*

/**
 * Creates a coroutine execution context using a single thread.
 */
@ExperimentalCoroutinesApi
public actual fun newSingleThreadContext(name: String): SingleThreadDispatcher =
    WorkerCoroutineDispatcherImpl(name).apply { start() }

/**
 * A coroutine dispatcher that is confined to a single thread.
 */
@ExperimentalCoroutinesApi
@Suppress("ACTUAL_WITHOUT_EXPECT")
public actual abstract class SingleThreadDispatcher : CoroutineDispatcher() {
    /**
     * A reference to this dispatcher's worker.
     */
    @ExperimentalCoroutinesApi
    public abstract val worker: Worker

    internal abstract val thread: Thread

    /**
     * Closes this coroutine dispatcher and shuts down its thread.
     */
    @ExperimentalCoroutinesApi
    public actual abstract fun close()
}

private class WorkerCoroutineDispatcherImpl(name: String) : SingleThreadDispatcher(), ThreadBoundInterceptor, Delay {
    override val worker = Worker.start(name = name)
    override val thread = WorkerThread(worker)
    private val isClosed = atomic(false)

    init { freeze() }

    fun start() {
        worker.execute {
            workerMain {
                runEventLoop(ThreadLocalEventLoop.eventLoop) { isClosed.value }
            }
        }
    }

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        checkCurrentThread()
        (ThreadLocalEventLoop.eventLoop as Delay).scheduleResumeAfterDelay(timeMillis, continuation)
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle {
        checkCurrentThread()
        return (ThreadLocalEventLoop.eventLoop as Delay).invokeOnTimeout(timeMillis, block, context)
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        checkCurrentThread()
        ThreadLocalEventLoop.eventLoop.dispatch(context, block)
    }

    override fun close() {
        isClosed.value = true
        worker.requestTermination().result // Note: calling "result" blocks
    }
}