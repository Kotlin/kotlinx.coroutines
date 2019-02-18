/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug.junit4

import kotlinx.coroutines.*
import kotlinx.coroutines.debug.*
import org.junit.runner.*
import org.junit.runners.model.*
import java.util.concurrent.*

internal class CoroutinesTimeoutStatement(
    private val testStatement: Statement, private val testDescription: Description,
    private val testTimeoutMs: Long,
    private val cancelOnTimeout: Boolean = false
) : Statement() {

    private val testExecutor = Executors.newSingleThreadExecutor {
        Thread(it).apply {
            name = "Timeout test executor"
            isDaemon = true
        }
    }

    // Thread to dump stack from, captured by testExecutor
    private lateinit var testThread: Thread

    override fun evaluate() {
        DebugProbes.install() // Fail-fast if probes are unavailable
        val latch = CountDownLatch(1)
        val testFuture = CompletableFuture.runAsync(Runnable {
            testThread = Thread.currentThread()
            latch.countDown()
            testStatement.evaluate()
        }, testExecutor)

        latch.await() // Await until test is started
        try {
            testFuture.get(testTimeoutMs, TimeUnit.MILLISECONDS)
            return
        } catch (e: TimeoutException) {
            handleTimeout(testDescription)
        } catch (e: ExecutionException) {
            throw e.cause ?: e
        } finally {
            DebugProbes.uninstall()
            testExecutor.shutdown()
        }
    }

    private fun handleTimeout(description: Description) {
        val units =
            if (testTimeoutMs % 1000L == 0L)
                "${testTimeoutMs / 1000} seconds"
            else "$testTimeoutMs milliseconds"

        val message = "Test ${description.methodName} timed out after $units"
        System.err.println("\n$message\n")
        System.err.flush()

        DebugProbes.dumpCoroutines()
        System.out.flush() // Synchronize serr/sout

        /*
         * Order is important:
         * 1) Create exception with a stacktrace of hang test
         * 2) Cancel all coroutines via debug agent API (changing system state!)
         * 3) Throw created exception
         */
        val exception = createTimeoutException(message, testThread)
        cancelIfNecessary()
        // If timed out test throws an exception, we can't do much except ignoring it
        throw exception
    }

    private fun cancelIfNecessary() {
        if (cancelOnTimeout) {
            DebugProbes.dumpCoroutinesState().forEach {
                it.jobOrNull?.cancel()
            }
        }
    }

    private fun createTimeoutException(message: String, thread: Thread): Exception {
        val stackTrace = thread.stackTrace
        val exception = TestTimedOutException(testTimeoutMs, TimeUnit.MILLISECONDS)
        exception.stackTrace = stackTrace
        thread.interrupt()
        return exception
    }
}
