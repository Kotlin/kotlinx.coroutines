/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.native.concurrent.*

@ExperimentalCoroutinesApi
public actual fun newSingleThreadContext(name: String): CloseableCoroutineDispatcher {
    return WorkerDispatcher(name)
}

public actual fun newFixedThreadPoolContext(nThreads: Int, name: String): CloseableCoroutineDispatcher {
    require(nThreads >= 1) { "Expected at least one thread, but got: $nThreads" }
    return MultiWorkerDispatcher(name, nThreads)
}

internal class WorkerDispatcher(name: String) : CloseableCoroutineDispatcher(), Delay {
    private val worker = Worker.start(name = name)

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        worker.executeAfter(0L) { block.run() }
    }

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val handle = schedule(timeMillis, Runnable {
            with(continuation) { resumeUndispatched(Unit) }
        })
        continuation.disposeOnCancellation(handle)
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle =
        schedule(timeMillis, block)

    private fun schedule(timeMillis: Long, block: Runnable): DisposableHandle {
        // Workers don't have an API to cancel sent "executeAfter" block, but we are trying
        // to control the damage and reduce reachable objects by nulling out `block`
        // that may retain a lot of references, and leaving only an empty shell after a timely disposal
        // This is a class and not an object with `block` in a closure because that would defeat the purpose.
        class DisposableBlock(block: Runnable) : DisposableHandle, Function0<Unit> {
            private val disposableHolder = AtomicReference<Runnable?>(block)

            override fun invoke() {
                disposableHolder.value?.run()
            }

            override fun dispose() {
                disposableHolder.value = null
            }
        }

        val disposableBlock = DisposableBlock(block)
        worker.executeAfter(timeMillis.toMicrosSafe(), disposableBlock)
        return disposableBlock
    }

    override fun close() {
        worker.requestTermination().result // Note: calling "result" blocks
    }

    private fun Long.toMicrosSafe(): Long {
        val result = this * 1000
        return if (result > this) result else Long.MAX_VALUE
    }
}

private class MultiWorkerDispatcher(
    private val name: String,
    workersCount: Int
) : CloseableCoroutineDispatcher() {
    private val tasksQueue = Channel<Runnable>(Channel.UNLIMITED)
    private val availableWorkers = Channel<CancellableContinuation<Runnable>>(Channel.UNLIMITED)
    private val workerPool = OnDemandAllocatingPool(workersCount) {
        Worker.start(name = "$name-$it").apply {
            executeAfter { workerRunLoop() }
        }
    }

    /**
     * (number of tasks - number of workers) * 2 + (1 if closed)
     */
    private val tasksAndWorkersCounter = atomic(0L)

    private inline fun Long.isClosed() = this and 1L == 1L
    private inline fun Long.hasTasks() = this >= 2
    private inline fun Long.hasWorkers() = this < 0

    private fun workerRunLoop() = runBlocking {
        while (true) {
            val state = tasksAndWorkersCounter.getAndUpdate {
                if (it.isClosed() && !it.hasTasks()) return@runBlocking
                it - 2
            }
            if (state.hasTasks()) {
                // we promised to process a task, and there are some
                tasksQueue.receive().run()
            } else {
                try {
                    suspendCancellableCoroutine {
                        val result = availableWorkers.trySend(it)
                        checkChannelResult(result)
                    }.run()
                } catch (e: CancellationException) {
                    /** we are cancelled from [close] and thus will never get back to this branch of code,
                    but there may still be pending work, so we can't just exit here. */
                }
            }
        }
    }

    // a worker that promised to be here and should actually arrive, so we wait for it in a blocking manner.
    private fun obtainWorker(): CancellableContinuation<Runnable> =
        availableWorkers.tryReceive().getOrNull() ?: runBlocking { availableWorkers.receive() }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        val state = tasksAndWorkersCounter.getAndUpdate {
            if (it.isClosed())
                throw IllegalStateException("Dispatcher $name was closed, attempted to schedule: $block")
            it + 2
        }
        if (state.hasWorkers()) {
            // there are workers that have nothing to do, let's grab one of them
            obtainWorker().resume(block)
        } else {
            workerPool.allocate()
            // no workers are available, we must queue the task
            val result = tasksQueue.trySend(block)
            checkChannelResult(result)
        }
    }

    override fun close() {
        tasksAndWorkersCounter.getAndUpdate { if (it.isClosed()) it else it or 1L }
        val workers = workerPool.close() // no new workers will be created
        while (true) {
            // check if there are workers that await tasks in their personal channels, we need to wake them up
            val state = tasksAndWorkersCounter.getAndUpdate {
                if (it.hasWorkers()) it + 2 else it
            }
            if (!state.hasWorkers())
                break
            obtainWorker().cancel()
        }
        /*
         * Here we cannot avoid waiting on `.result`, otherwise it will lead
         * to a native memory leak, including a pthread handle.
         */
        val requests = workers.map { it.requestTermination() }
        requests.map { it.result }
    }

    private fun checkChannelResult(result: ChannelResult<*>) {
        if (!result.isSuccess)
            throw IllegalStateException(
                "Internal invariants of $this were violated, please file a bug to kotlinx.coroutines",
                result.exceptionOrNull()
            )
    }
}
