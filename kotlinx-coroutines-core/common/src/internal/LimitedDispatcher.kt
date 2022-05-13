/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.jvm.*

/**
 * The result of .limitedParallelism(x) call, a dispatcher
 * that wraps the given dispatcher, but limits the parallelism level, while
 * trying to emulate fairness.
 */
internal class LimitedDispatcher(
    private val dispatcher: CoroutineDispatcher,
    private val parallelism: Int
) : CoroutineDispatcher(), Runnable, Delay by (dispatcher as? Delay ?: DefaultDelay) {

    @Volatile
    private var runningWorkers = 0

    private val queue = LockFreeTaskQueue<Runnable>(singleConsumer = false)

    // A separate object that we can synchronize on for K/N
    private val workerAllocationLock = SynchronizedObject()

    @ExperimentalCoroutinesApi
    override fun limitedParallelism(parallelism: Int): CoroutineDispatcher {
        parallelism.checkParallelism()
        if (parallelism >= this.parallelism) return this
        return super.limitedParallelism(parallelism)
    }

    override fun run() {
        var fairnessCounter = 0
        while (true) {
            val task = queue.removeFirstOrNull()
            if (task != null) {
                try {
                    task.run()
                } catch (e: Throwable) {
                    handleCoroutineException(EmptyCoroutineContext, e)
                }
                // 16 is our out-of-thin-air constant to emulate fairness. Used in JS dispatchers as well
                if (++fairnessCounter >= 16 && dispatcher.isDispatchNeeded(this)) {
                    // Do "yield" to let other views to execute their runnable as well
                    // Note that we do not decrement 'runningWorkers' as we still committed to do our part of work
                    dispatcher.dispatch(this, this)
                    return
                }
                continue
            }

            synchronized(workerAllocationLock) {
                --runningWorkers
                if (queue.size == 0) return
                ++runningWorkers
                fairnessCounter = 0
            }
        }
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        dispatchInternal(block) {
            dispatcher.dispatch(this, this)
        }
    }

    @InternalCoroutinesApi
    override fun dispatchYield(context: CoroutineContext, block: Runnable) {
        dispatchInternal(block) {
            dispatcher.dispatchYield(this, this)
        }
    }

    private inline fun dispatchInternal(block: Runnable, dispatch: () -> Unit) {
        // Add task to queue so running workers will be able to see that
        if (addAndTryDispatching(block)) return
        /*
         * Protect against the race when the number of workers is enough,
         * but one (because of synchronized serialization) attempts to complete,
         * and we just observed the number of running workers smaller than the actual
         * number (hit right between `--runningWorkers` and `++runningWorkers` in `run()`)
         */
        if (!tryAllocateWorker()) return
        dispatch()
    }

    private fun tryAllocateWorker(): Boolean {
        synchronized(workerAllocationLock) {
            if (runningWorkers >= parallelism) return false
            ++runningWorkers
            return true
        }
    }

    private fun addAndTryDispatching(block: Runnable): Boolean {
        queue.addLast(block)
        return runningWorkers >= parallelism
    }
}

// Save a few bytecode ops
internal fun Int.checkParallelism() = require(this >= 1) { "Expected positive parallelism level, but got $this" }
