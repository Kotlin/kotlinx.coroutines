package kotlinx.coroutines.internal

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.scheduling.ParallelismCompensation
import kotlin.coroutines.*

/**
 * Introduced as part of IntelliJ patches.
 *
 * CoroutineDispatchers may optionally implement this interface to declare an ability to construct [SoftLimitedDispatcher]
 * on top of themselves. This is not possible in general case, because the worker of the underlying dispatcher must
 * implement [ParallelismCompensation] and properly propagate such requests to the task it is running.
 */
internal interface SoftLimitedParallelism {
    fun softLimitedParallelism(parallelism: Int): CoroutineDispatcher
}

/**
 * Introduced as part of IntelliJ patches.
 */
internal fun CoroutineDispatcher.softLimitedParallelism(parallelism: Int): CoroutineDispatcher {
    if (this is SoftLimitedParallelism) {
        return this.softLimitedParallelism(parallelism)
    }
    // SoftLimitedDispatcher cannot be used on top of LimitedDispatcher, because the latter doesn't propagate compensation requests
    throw UnsupportedOperationException("CoroutineDispatcher.softLimitedParallelism cannot be applied to $this")
}

/**
 * Introduced as part of IntelliJ patches.
 *
 * Shamelessly copy-pasted from [LimitedDispatcher], but [ParallelismCompensation] is
 * implemented for [Worker] to allow compensation.
 *
 * [ParallelismCompensation] breaks the contract of [LimitedDispatcher] so a separate class is made to implement a
 * dispatcher that mostly behaves as limited, but can temporarily increase parallelism if necessary.
 */
internal class SoftLimitedDispatcher(
    private val dispatcher: CoroutineDispatcher,
    parallelism: Int
) : CoroutineDispatcher(), Delay by (dispatcher as? Delay ?: DefaultDelay), SoftLimitedParallelism {
    private val initialParallelism = parallelism
    // `parallelism limit - runningWorkers`; may be < 0 if decompensation is expected
    private val availablePermits = atomic(parallelism)

    private val queue = LockFreeTaskQueue<Runnable>(singleConsumer = false)

    private val workerAllocationLock = SynchronizedObject()

    override fun limitedParallelism(parallelism: Int): CoroutineDispatcher {
        return super.limitedParallelism(parallelism)
    }

    override fun softLimitedParallelism(parallelism: Int): CoroutineDispatcher {
        parallelism.checkParallelism()
        if (parallelism >= initialParallelism) return this
        return SoftLimitedDispatcher(this, parallelism)
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        dispatchInternal(block) { worker ->
            dispatcher.dispatch(this, worker)
        }
    }

    @InternalCoroutinesApi
    override fun dispatchYield(context: CoroutineContext, block: Runnable) {
        dispatchInternal(block) { worker ->
            dispatcher.dispatchYield(this, worker)
        }
    }

    /**
     * Tries to dispatch the given [block].
     * If there are not enough workers, it starts a new one via [startWorker].
     */
    private inline fun dispatchInternal(block: Runnable, startWorker: (Worker) -> Unit) {
        queue.addLast(block)
        if (availablePermits.value <= 0) return
        if (!tryAllocateWorker()) return
        val task = obtainTaskOrDeallocateWorker() ?: return
        startWorker(Worker(task))
    }

    /**
     * Tries to obtain the permit to start a new worker.
     */
    private fun tryAllocateWorker(): Boolean {
        synchronized(workerAllocationLock) {
            val permits = availablePermits.value
            if (permits <= 0) return false
            return availablePermits.compareAndSet(permits, permits - 1)
        }
    }

    /**
     * Obtains the next task from the queue, or logically deallocates the worker if the queue is empty.
     */
    private fun obtainTaskOrDeallocateWorker(): Runnable? {
        val permits = availablePermits.value
        if (permits < 0) { // decompensation
            if (availablePermits.compareAndSet(permits, permits + 1)) return null
        }
        while (true) {
            when (val nextTask = queue.removeFirstOrNull()) {
                null -> synchronized(workerAllocationLock) {
                    availablePermits.incrementAndGet()
                    if (queue.size == 0) return null
                    availablePermits.decrementAndGet()
                }
                else -> return nextTask
            }
        }
    }

    /**
     * Every running Worker holds a permit
     */
    private inner class Worker(private var currentTask: Runnable) : Runnable, ParallelismCompensation {
        override fun run() {
            var fairnessCounter = 0
            while (true) {
                try {
                    currentTask.run()
                } catch (e: Throwable) {
                    handleCoroutineException(EmptyCoroutineContext, e)
                }
                currentTask = obtainTaskOrDeallocateWorker() ?: return
                // 16 is our out-of-thin-air constant to emulate fairness. Used in JS dispatchers as well
                if (++fairnessCounter >= 16 && dispatcher.isDispatchNeeded(this@SoftLimitedDispatcher)) {
                    // Do "yield" to let other views execute their runnable as well
                    // Note that we do not decrement 'runningWorkers' as we are still committed to our part of work
                    dispatcher.dispatch(this@SoftLimitedDispatcher, this)
                    return
                }
            }
        }

        override fun increaseParallelismAndLimit() {
            val newTask = obtainTaskOrDeallocateWorker() // either increases the number of permits or we launch a new worker (which holds a permit)
            if (newTask != null) {
                dispatcher.dispatch(this@SoftLimitedDispatcher, Worker(newTask))
            }
            (currentTask as? ParallelismCompensation)?.increaseParallelismAndLimit()
        }

        override fun decreaseParallelismLimit() {
            try {
                (currentTask as? ParallelismCompensation)?.decreaseParallelismLimit()
            } finally {
                availablePermits.decrementAndGet()
            }
        }
    }
}