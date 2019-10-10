/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import org.junit.*
import org.junit.Test
import java.util.concurrent.*
import java.util.concurrent.atomic.*
import kotlin.coroutines.*
import kotlin.test.*

class CoroutineSchedulerStressTest : TestBase() {
    private var dispatcher: ExperimentalCoroutineDispatcher = ExperimentalCoroutineDispatcher()
    private val observedThreads = ConcurrentHashMap<Thread, Long>()
    private val tasksNum = 500_000 * stressMemoryMultiplier()

    private fun stressMemoryMultiplier(): Int {
        return if (isStressTest) {
            AVAILABLE_PROCESSORS * 4
        } else {
            1
        }
    }

    private val processed = AtomicInteger(0)
    private val finishLatch = CountDownLatch(1)

    @After
    fun tearDown() {
        dispatcher.close()
    }

    @Test
    fun testInternalTasksSubmissionProgress() {
        /*
       * Run 2 million tasks and validate that
       * 1) All of them are completed successfully
       * 2) Every thread executed task at least once
       */
        dispatcher.dispatch(EmptyCoroutineContext, Runnable {
            for (i in 1..tasksNum) {
                dispatcher.dispatch(EmptyCoroutineContext, ValidatingRunnable())
            }
        })

        finishLatch.await()
        val observed = observedThreads.size
        // on slow machines not all threads can be observed
        assertTrue(observed in (AVAILABLE_PROCESSORS - 1)..(AVAILABLE_PROCESSORS + 1), "Observed $observed threads with $AVAILABLE_PROCESSORS available processors")
        validateResults()
    }

    @Test
    fun testStealingFromNonProgressing() {
        /*
         * Work-stealing stress test,
         * one thread submits pack of tasks, waits until they are completed (to avoid work offloading)
         * and then repeats, thus never executing its own tasks and relying only on work stealing.
         */
        var blockingThread: Thread? = null
        dispatcher.dispatch(EmptyCoroutineContext, Runnable {
            // Submit million tasks
            blockingThread = Thread.currentThread()
            var submittedTasks = 0
            while (submittedTasks < tasksNum) {

                ++submittedTasks
                dispatcher.dispatch(EmptyCoroutineContext, ValidatingRunnable())
                while (submittedTasks - processed.get() > 100) {
                    Thread.yield()
                }
            }

            // Block current thread
            finishLatch.await()
        })

        finishLatch.await()

        require(!observedThreads.containsKey(blockingThread!!))
        validateResults()
    }

    private fun processTask() {
        val counter = observedThreads[Thread.currentThread()] ?: 0L
        observedThreads[Thread.currentThread()] = counter + 1

        if (processed.incrementAndGet() == tasksNum) {
            finishLatch.countDown()
        }
    }

    private fun validateResults() {
        val result = observedThreads.values.sum()
        assertEquals(tasksNum.toLong(), result)
    }

    private inner class ValidatingRunnable : Runnable {
        private val invoked = atomic(false)
        override fun run() {
            if (!invoked.compareAndSet(false, true)) error("The same runnable was invoked twice")
            processTask()
        }
    }
}
