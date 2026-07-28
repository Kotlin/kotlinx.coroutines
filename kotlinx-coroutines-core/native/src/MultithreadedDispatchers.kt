@file:OptIn(ObsoleteWorkersApi::class)

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.concurrent.AtomicReference
import kotlin.native.concurrent.*
import kotlin.time.*
import kotlin.time.Duration.Companion.milliseconds

@DelicateCoroutinesApi
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

            fun isDisposed() = disposableHolder.value == null
        }

        fun Worker.runAfterDelay(block: DisposableBlock, targetMoment: TimeMark) {
            if (block.isDisposed()) return
            val durationUntilTarget = -targetMoment.elapsedNow()
            val quantum = 100.milliseconds
            if (durationUntilTarget > quantum) {
                executeAfter(quantum.inWholeMicroseconds) { runAfterDelay(block, targetMoment) }
            } else {
                executeAfter(maxOf(0, durationUntilTarget.inWholeMicroseconds), block)
            }
        }

        val disposableBlock = DisposableBlock(block)
        val targetMoment = TimeSource.Monotonic.markNow() + timeMillis.milliseconds
        worker.runAfterDelay(disposableBlock, targetMoment)
        return disposableBlock
    }

    override fun close() {
        worker.requestTermination().result // Note: calling "result" blocks
    }
}

private class MultiWorkerDispatcher(
    private val name: String,
    private val workersCount: Int
) : CloseableCoroutineDispatcher() {
    private val tasksQueue = Channel<Runnable>(Channel.UNLIMITED)
    private val workerPool = OnDemandAllocatingPool<Worker>(workersCount)

    /**
     * `number of tasks - number of workers`.
     *
     * Used only to determine if we need to allocate a new worker when a new task arrives: if there are idling workers,
     * we can reuse them.
     *
     * It is safe for this variable to overflow.
     * For [tasksMinusWorkers] to exceed [Int.MAX_VALUE], we need to have at least [Int.MAX_VALUE] tasks enqueued,
     * each of which requested a worker allocation.
     * Even in the (practically impossible) race with [workersCount] being [Int.MAX_VALUE],
     * we will correctly allocate every worker.
     */
    private val tasksMinusWorkers = atomic(0)

    private fun workerRunLoop() = runBlocking {
        while (true) {
            tasksMinusWorkers.getAndAdd(-1)
            tasksQueue.receiveCatching()
                .onSuccess { it.run() }
                .onClosed { return@runBlocking }
        }
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        val previousTasksMinusWorkers = tasksMinusWorkers.getAndAdd(1)
        if (previousTasksMinusWorkers >= 0) {
            // no workers are available, we must allocate a new one
            var worker: Worker? = null
            val allocated = workerPool.allocate {
                Worker.start(name = "$name-$it").also { worker = it }
            }
            if (worker != null) {
                if (allocated) {
                    worker.executeAfter { workerRunLoop() }
                } else {
                    worker.requestTermination().result
                }
            }
        }
        tasksQueue.trySend(block)
            .onClosed {
                tasksMinusWorkers.getAndAdd(-1) // remove the task we failed to send
                error("Dispatcher $name was closed, attempted to schedule: $block")
            }
    }

    override fun limitedParallelism(parallelism: Int, name: String?): CoroutineDispatcher {
        parallelism.checkParallelism()
        if (parallelism >= workersCount) {
            return namedOrThis(name)
        }
        return super.limitedParallelism(parallelism, name)
    }

    override fun close() {
        // the order is important: we don't want to end up with a non-empty channel because there are no workers
        tasksQueue.close()
        val workers = workerPool.close() // no new workers will be created
        /*
         * Here we cannot avoid waiting on `.result`, otherwise it will lead
         * to a native memory leak, including a pthread handle.
         */
        val requests = workers.map { it.requestTermination() }
        requests.forEach { it.result }
    }
}
