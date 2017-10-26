/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package guide.test

import kotlinx.coroutines.experimental.*
import org.junit.Assert.assertEquals
import org.junit.Assert.assertTrue
import java.io.ByteArrayInputStream
import java.io.ByteArrayOutputStream
import java.io.OutputStream
import java.io.PrintStream
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.TimeUnit
import java.util.concurrent.locks.LockSupport

fun trackTask(block: Runnable) = timeSource.trackTask(block)

// helper function to dump exception to stdout for ease of debugging failed tests
private inline fun <T> outputException(name: String, block: () -> T): T =
    try { block() }
    catch (e: Throwable) {
        println("--- Failed test$name")
        e.printStackTrace(System.out)
        throw e
    }

private const val SHUTDOWN_TIMEOUT = 5000L // 5 sec at most to wait

fun test(name: String, block: () -> Unit): List<String> = outputException(name) {
    println("--- Running test$name")
    val oldOut = System.out
    val oldErr = System.err
    val bytesOut = ByteArrayOutputStream()
    val tee = TeeOutput(bytesOut, oldOut)
    val ps = PrintStream(tee)
    System.setErr(ps)
    System.setOut(ps)
    CommonPool.usePrivatePool()
    resetCoroutineId()
    // shutdown execution with old time source (in case it was working)
    DefaultExecutor.shutdown(SHUTDOWN_TIMEOUT)
    val threadsBefore = currentThreads()
    val testTimeSource = TestTimeSource(oldOut)
    timeSource = testTimeSource
    DefaultExecutor.ensureStarted() // should start with new time source
    val bytes: ByteArray
    try {
        block()
    } catch (e: Throwable) {
        System.err.print("Exception in thread \"main\" ")
        e.printStackTrace()
    } finally {
        // capture output
        bytes = bytesOut.toByteArray()
        oldOut.println("--- shutting down")
        // the shutdown
        CommonPool.shutdown(SHUTDOWN_TIMEOUT)
        shutdownDispatcherPools(SHUTDOWN_TIMEOUT)
        DefaultExecutor.shutdown(SHUTDOWN_TIMEOUT) // the last man standing -- cleanup all pending tasks
        testTimeSource.shutdown()
        timeSource = DefaultTimeSource // restore time source
        CommonPool.restore()
        if (tee.flushLine()) oldOut.println()
        oldOut.println("--- done")
        System.setOut(oldOut)
        System.setErr(oldErr)
        checkTestThreads(threadsBefore)
    }
    return ByteArrayInputStream(bytes).bufferedReader().readLines()
}

private class TeeOutput(
    private val bytesOut: OutputStream,
    private val oldOut: PrintStream
) : OutputStream() {
    val limit = 200
    var lineLength = 0

    fun flushLine(): Boolean {
        if (lineLength > limit)
            oldOut.print(" ($lineLength chars in total)")
        val result = lineLength > 0
        lineLength = 0
        return result
    }

    override fun write(b: Int) {
        bytesOut.write(b)
        if (b == 0x0d || b == 0x0a) { // new line
            flushLine()
            oldOut.write(b)
        } else {
            lineLength++
            if (lineLength <= limit)
                oldOut.write(b)
        }
    }
}

private val NOT_PARKED = -1L

private class ThreadStatus {
    @Volatile @JvmField
    var parkedTill = NOT_PARKED
    @Volatile @JvmField
    var permit = false
    override fun toString(): String = "parkedTill = ${TimeUnit.NANOSECONDS.toMillis(parkedTill)} ms, permit = $permit"
}

private val MAX_WAIT_NANOS = 10_000_000_000L // 10s
private val REAL_TIME_STEP_NANOS = 200_000_000L // 200 ms
private val REAL_PARK_NANOS = 10_000_000L // 10 ms -- park for a little to better track real-time

@Suppress("PLATFORM_CLASS_MAPPED_TO_KOTLIN")
private class TestTimeSource(
    private val log: PrintStream
) : TimeSource {
    private val mainThread: Thread = Thread.currentThread()
    private var checkpointNanos: Long = System.nanoTime()

    @Volatile
    private var isShutdown = false

    @Volatile
    private var time: Long = 0

    private var trackedTasks = 0

    private val threads = ConcurrentHashMap<Thread, ThreadStatus>()

    override fun nanoTime(): Long = time

    @Synchronized
    override fun trackTask(block: Runnable): Runnable {
        trackedTasks++
        return Runnable {
            try { block.run() }
            finally { unTrackTask() }
        }
    }

    @Synchronized
    override fun unTrackTask() {
        assert(trackedTasks > 0)
        trackedTasks--
    }

    @Synchronized
    override fun registerTimeLoopThread() {
        assert(threads.putIfAbsent(Thread.currentThread(), ThreadStatus()) == null)
    }

    @Synchronized
    override fun unregisterTimeLoopThread() {
        assert(threads.remove(Thread.currentThread()) != null)
        wakeupAll()
    }

    override fun parkNanos(blocker: Any, nanos: Long) {
        if (nanos <= 0) return
        val status = threads[Thread.currentThread()]!!
        assert(status.parkedTill == NOT_PARKED)
        status.parkedTill = time + nanos.coerceAtMost(MAX_WAIT_NANOS)
        while (true) {
            checkAdvanceTime()
            if (isShutdown || time >= status.parkedTill || status.permit) {
                status.parkedTill = NOT_PARKED
                status.permit = false
                break
            }
            LockSupport.parkNanos(blocker, REAL_PARK_NANOS)
        }
    }

    override fun unpark(thread: Thread) {
        val status = threads[thread] ?: return
        status.permit = true
        LockSupport.unpark(thread)
    }

    @Synchronized
    private fun checkAdvanceTime() {
        if (isShutdown) return
        val realNanos = System.nanoTime()
        if (realNanos > checkpointNanos + REAL_TIME_STEP_NANOS) {
            checkpointNanos = realNanos
            val minParkedTill = minParkedTill()
            time = (time + REAL_TIME_STEP_NANOS).coerceAtMost(if (minParkedTill < 0) Long.MAX_VALUE else minParkedTill)
            logTime("R")
            wakeupAll()
            return
        }
        if (threads[mainThread] == null) return
        if (trackedTasks != 0) return
        val minParkedTill = minParkedTill()
        if (minParkedTill <= time) return
        time = minParkedTill
        logTime("V")
        wakeupAll()
    }

    private fun logTime(s: String) {
        log.println("[$s: Time = ${TimeUnit.NANOSECONDS.toMillis(time)} ms]")
    }

    private fun minParkedTill(): Long =
        threads.values.map { if (it.permit) NOT_PARKED else it.parkedTill }.min() ?: NOT_PARKED

    @Synchronized
    fun shutdown() {
        isShutdown = true
        wakeupAll()
        while (!threads.isEmpty()) (this as Object).wait()
    }

    private fun wakeupAll() {
        threads.keys.forEach { LockSupport.unpark(it) }
        (this as Object).notifyAll()
    }
}

private fun shutdownDispatcherPools(timeout: Long) {
    val threads = arrayOfNulls<Thread>(Thread.activeCount())
    val n = Thread.enumerate(threads)
    for (i in 0 until n) {
        val thread = threads[i]
        if (thread is PoolThread)
            thread.dispatcher.executor.apply {
                shutdown()
                awaitTermination(timeout, TimeUnit.MILLISECONDS)
                shutdownNow().forEach { DefaultExecutor.execute(it) }
            }
    }
}

enum class SanitizeMode {
    NONE,
    ARBITRARY_TIME,
    FLEXIBLE_THREAD
}

private fun sanitize(s: String, mode: SanitizeMode): String {
    var res = s
    when (mode) {
        SanitizeMode.ARBITRARY_TIME -> {
            res = res.replace(Regex(" [0-9]+ ms"), " xxx ms")
        }
        SanitizeMode.FLEXIBLE_THREAD -> {
            res = res.replace(Regex("ForkJoinPool\\.commonPool-worker-[0-9]+"), "CommonPool")
            res = res.replace(Regex("ForkJoinPool-[0-9]+-worker-[0-9]+"), "CommonPool")
            res = res.replace(Regex("CommonPool-worker-[0-9]+"), "CommonPool")
            res = res.replace(Regex("RxComputationThreadPool-[0-9]+"), "RxComputationThreadPool")
            res = res.replace(Regex("Test( worker)?"), "main")
        }
        SanitizeMode.NONE -> {}
    }
    return res
}

private fun List<String>.verifyCommonLines(expected: Array<out String>, mode: SanitizeMode = SanitizeMode.NONE) {
    val n = minOf(size, expected.size)
    for (i in 0 until n) {
        val exp = sanitize(expected[i], mode)
        val act = sanitize(get(i), mode)
        assertEquals("Line ${i + 1}", exp, act)
    }
}

private fun List<String>.checkEqualNumberOfLines(expected: Array<out String>) {
    if (size > expected.size)
        error("Expected ${expected.size} lines, but found $size. Unexpected line '${get(expected.size)}'")
    else if (size < expected.size)
        error("Expected ${expected.size} lines, but found $size")
}

fun List<String>.verifyLines(vararg expected: String) {
    verifyCommonLines(expected)
    checkEqualNumberOfLines(expected)
}

fun List<String>.verifyLinesStartWith(vararg expected: String) {
    verifyCommonLines(expected)
    assertTrue("Number of lines", expected.size <= size)
}

fun List<String>.verifyLinesArbitraryTime(vararg expected: String) {
    verifyCommonLines(expected, SanitizeMode.ARBITRARY_TIME)
    checkEqualNumberOfLines(expected)
}

fun List<String>.verifyLinesFlexibleThread(vararg expected: String) {
    verifyCommonLines(expected, SanitizeMode.FLEXIBLE_THREAD)
    checkEqualNumberOfLines(expected)
}

fun List<String>.verifyLinesStartUnordered(vararg expected: String) {
    val expectedSorted = expected.sorted().toTypedArray()
    sorted().verifyLinesStart(*expectedSorted)
}

fun List<String>.verifyLinesStart(vararg expected: String) {
    val n = minOf(size, expected.size)
    for (i in 0 until n) {
        val exp = sanitize(expected[i], SanitizeMode.FLEXIBLE_THREAD)
        val act = sanitize(get(i), SanitizeMode.FLEXIBLE_THREAD)
        assertEquals("Line ${i + 1}", exp, act.substring(0, minOf(act.length, exp.length)))
    }
    checkEqualNumberOfLines(expected)
}