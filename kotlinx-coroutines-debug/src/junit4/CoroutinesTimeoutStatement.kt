/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug.junit4

import kotlinx.coroutines.debug.*
import org.junit.runner.*
import org.junit.runners.model.*
import java.util.concurrent.*

internal class CoroutinesTimeoutStatement(
    testStatement: Statement,
    private val testDescription: Description,
    private val testTimeoutMs: Long,
    private val cancelOnTimeout: Boolean = false
) : Statement() {

    private val testStartedLatch = CountDownLatch(1)

    private val testResult = FutureTask<Unit> {
        testStartedLatch.countDown()
        testStatement.evaluate()
    }

    /*
     * We are using hand-rolled thread instead of single thread executor
     * in order to be able to safely interrupt thread in the end of a test
     */
    private val testThread =  Thread(testResult, "Timeout test thread").apply { isDaemon = true }

    override fun evaluate() {
        try {
            testThread.start()
            // Await until test is started to take only test execution time into account
            testStartedLatch.await()
            testResult.get(testTimeoutMs, TimeUnit.MILLISECONDS)
            return
        } catch (e: TimeoutException) {
            handleTimeout(testDescription)
        } catch (e: ExecutionException) {
            throw e.cause ?: e
        } finally {
            DebugProbes.uninstall()
        }
    }

    private fun handleTimeout(description: Description) {
        val units =
            if (testTimeoutMs % 1000 == 0L)
                "${testTimeoutMs / 1000} seconds"
            else "$testTimeoutMs milliseconds"

        System.err.println("\nTest ${description.methodName} timed out after $units\n")
        System.err.flush()

        DebugProbes.dumpCoroutines()
        System.out.flush() // Synchronize serr/sout

        /*
         * Order is important:
         * 1) Create exception with a stacktrace of hang test
         * 2) Cancel all coroutines via debug agent API (changing system state!)
         * 3) Throw created exception
         */
        val exception = createTimeoutException(testThread)
        cancelIfNecessary()
        // If timed out test throws an exception, we can't do much except ignoring it
        throw exception
    }

    private fun cancelIfNecessary() {
        if (cancelOnTimeout) {
            DebugProbes.dumpCoroutinesInfo().forEach {
                it.job?.cancel()
            }
        }
    }

    private fun createTimeoutException(thread: Thread): Exception {
        val stackTrace = thread.stackTrace
        val exception = TestTimedOutException(testTimeoutMs, TimeUnit.MILLISECONDS)
        exception.stackTrace = stackTrace
        thread.interrupt()
        return exception
    }
}
