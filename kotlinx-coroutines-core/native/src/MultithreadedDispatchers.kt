/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.channels.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.native.concurrent.*

@ExperimentalCoroutinesApi
public actual fun newSingleThreadContext(name: String): CloseableCoroutineDispatcher {
    if (!multithreadingSupported) throw IllegalStateException("This API is only supported for experimental K/N memory model")
    return WorkerDispatcher(name)
}

public actual fun newFixedThreadPoolContext(nThreads: Int, name: String): CloseableCoroutineDispatcher {
    if (!multithreadingSupported) throw IllegalStateException("This API is only supported for experimental K/N memory model")
    require(nThreads >= 1) { "Expected at least one thread, but got: $nThreads"}
    return MultiWorkerDispatcher(name, nThreads)
}

internal class WorkerDispatcher(name: String) : CloseableCoroutineDispatcher(), Delay {
    private val worker = Worker.start(name = name)

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        worker.executeAfter(0L) { block.run() }
    }

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        worker.executeAfter(timeMillis.toMicrosSafe()) {
            with(continuation) { resumeUndispatched(Unit) }
        }
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle {
        // No API to cancel on timeout
        worker.executeAfter(timeMillis.toMicrosSafe()) { block.run() }
        return NonDisposableHandle
    }

    override fun close() {
        worker.requestTermination().result // Note: calling "result" blocks
    }

    private fun Long.toMicrosSafe(): Long {
        val result = this * 1000
        return if (result > this) result else Long.MAX_VALUE
    }
}

private class MultiWorkerDispatcher(name: String, workersCount: Int) : CloseableCoroutineDispatcher() {
    private val tasksQueue = Channel<Runnable>(Channel.UNLIMITED)
    private val workers = Array(workersCount) { Worker.start(name = "$name-$it") }

    init {
        workers.forEach { w -> w.executeAfter(0L) { workerRunLoop() } }
    }

    private fun workerRunLoop() = runBlocking {
        for (task in tasksQueue) {
            // TODO error handling
            task.run()
        }
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        // TODO handle rejections
        tasksQueue.trySend(block)
    }

    override fun close() {
        tasksQueue.close()
        workers.forEach { it.requestTermination().result }
    }
}
