/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.scheduling

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.scheduling.SchedulerTestBase.Companion.checkPoolThreadsCreated
import org.junit.*
import org.junit.Test
import java.util.concurrent.*
import java.util.concurrent.atomic.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

class CoroutineSchedulerStressTest : TestBase() {

    private var dispatcher: ExperimentalCoroutineDispatcher = ExperimentalCoroutineDispatcher()
    private val observedThreads = ConcurrentHashMap<Thread, Long>()
    private val tasksNum = 2_000_000 * stressTestMultiplier
    private val processed = AtomicInteger(0)
    private val finishLatch = CountDownLatch(1)

    @After
    fun tearDown() {
        dispatcher.close()
    }

    @Test
    fun testExternalTasksSubmission() {
        stressTest(CommonPool)
    }

    @Test
    fun testInternalTasksSubmission() {
        stressTest(dispatcher)
    }

    @Test
    fun testStealingFromBlocking() {
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
            val processedCounter = AtomicLong(0)
            while (submittedTasks <= tasksNum) {
                for (i in 1..120) {
                    if (++submittedTasks > tasksNum) {
                        // Block current thread
                        finishLatch.await()
                        return@Runnable
                    }

                    dispatcher.dispatch(EmptyCoroutineContext, Runnable {
                        processTask()
                        processedCounter.incrementAndGet()
                    })
                }

                while (processedCounter.get() < 100) {
                    Thread.yield()
                }

                processedCounter.set(0L)
            }
        })

        finishLatch.await()

        require(blockingThread!! !in observedThreads)
        validateResults()
    }

    private fun stressTest(submissionInitiator: CoroutineDispatcher) {
        /*
         * Run 1 million tasks and validate that
         * 1) All of them are completed successfully
         * 2) Every thread executed task at least once
         */
        submissionInitiator.dispatch(EmptyCoroutineContext, Runnable {
            for (i in 1..tasksNum) {
                dispatcher.dispatch(EmptyCoroutineContext, Runnable {
                    processTask()
                })
            }
        })

        finishLatch.await()
        assertEquals(Runtime.getRuntime().availableProcessors(), observedThreads.size)
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
        checkPoolThreadsCreated(Runtime.getRuntime().availableProcessors())
    }

}
