/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug

import java.util.concurrent.*

/**
 * Run [invocation] in a separate thread with the given timeout in ms, after which the coroutines info is dumped and, if
 * [cancelOnTimeout] is set, the execution is interrupted.
 *
 * Assumes that [DebugProbes] are installed. Does not deinstall them.
 */
internal inline fun <T : Any?> runWithTimeoutDumpingCoroutines(
    methodName: String,
    testTimeoutMs: Long,
    cancelOnTimeout: Boolean,
    initCancellationException: () -> Throwable,
    crossinline invocation: () -> T
): T {
    val testStartedLatch = CountDownLatch(1)
    val testResult = FutureTask {
        testStartedLatch.countDown()
        invocation()
    }
    /*
     * We are using hand-rolled thread instead of single thread executor
     * in order to be able to safely interrupt thread in the end of a test
     */
    val testThread = Thread(testResult, "Timeout test thread").apply { isDaemon = true }
    try {
        testThread.start()
        // Await until test is started to take only test execution time into account
        testStartedLatch.await()
        return testResult.get(testTimeoutMs, TimeUnit.MILLISECONDS)
    } catch (e: TimeoutException) {
        handleTimeout(testThread, methodName, testTimeoutMs, cancelOnTimeout, initCancellationException())
    } catch (e: ExecutionException) {
        throw e.cause ?: e
    }
}

private fun handleTimeout(testThread: Thread, methodName: String, testTimeoutMs: Long, cancelOnTimeout: Boolean,
                          cancellationException: Throwable): Nothing {
    val units =
        if (testTimeoutMs % 1000 == 0L)
            "${testTimeoutMs / 1000} seconds"
        else "$testTimeoutMs milliseconds"

    System.err.println("\nTest $methodName timed out after $units\n")
    System.err.flush()

    DebugProbes.dumpCoroutines()
    System.out.flush() // Synchronize serr/sout

    /*
     * Order is important:
     * 1) Create exception with a stacktrace of hang test
     * 2) Cancel all coroutines via debug agent API (changing system state!)
     * 3) Throw created exception
     */
    cancellationException.attachStacktraceFrom(testThread)
    testThread.interrupt()
    cancelIfNecessary(cancelOnTimeout)
    // If timed out test throws an exception, we can't do much except ignoring it
    throw cancellationException
}

private fun cancelIfNecessary(cancelOnTimeout: Boolean) {
    if (cancelOnTimeout) {
        DebugProbes.dumpCoroutinesInfo().forEach {
            it.job?.cancel()
        }
    }
}

private fun Throwable.attachStacktraceFrom(thread: Thread) {
    val stackTrace = thread.stackTrace
    this.stackTrace = stackTrace
}
