/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.channels.*
import kotlin.coroutines.*
import kotlin.native.concurrent.*

@ExperimentalCoroutinesApi
public actual fun newSingleThreadContext(name: String): CloseableCoroutineDispatcher {
    return WorkerDispatcher(name)
}

public actual fun newFixedThreadPoolContext(nThreads: Int, name: String): CloseableCoroutineDispatcher {
    require(nThreads >= 1) { "Expected at least one thread, but got: $nThreads"}
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
    private val workersCount: Int
) : CloseableCoroutineDispatcher() {
    private val tasksQueue = Channel<Runnable>(Channel.UNLIMITED)
    private val workers = atomicArrayOfNulls<Worker>(workersCount)
    private val activeWorkers = atomic(0)

    private fun workerRunLoop() = runBlocking {
        for (task in tasksQueue) {
            /**
             * Any unhandled exception here will pass through worker's boundary and will be properly reported.
             */
            task.run()
        }
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        if (activeWorkers.value != workersCount) {
            tryAddWorker()
        }

        tasksQueue.trySend(block).onClosed {
            throw IllegalStateException("Dispatcher $name was closed, attempted to schedule : $block")
        }
    }

    private fun tryAddWorker() {
        activeWorkers.loop { curWorkers ->
            if (curWorkers >= workersCount) return
            if (activeWorkers.compareAndSet(curWorkers, curWorkers + 1)) {
                val worker = Worker.start(name = "$name-$curWorkers")
                worker.executeAfter { workerRunLoop() }
                workers[curWorkers].value = worker
                return
            }
        }
    }

    override fun close() {
        tasksQueue.close()
        /*
         * Here we cannot avoid waiting on `.result`, otherwise it will lead
         * to a native memory leak, including a pthread handle.
         */
        val requests = Array(workersCount) {
            workers[it].value?.requestTermination()
        }
        requests.map { it?.result }
    }
}
