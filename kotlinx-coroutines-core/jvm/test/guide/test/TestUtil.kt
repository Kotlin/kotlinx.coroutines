/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.guide.test

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.scheduling.*
import java.io.*
import java.util.concurrent.*
import kotlin.test.*

fun wrapTask(block: Runnable) = kotlinx.coroutines.wrapTask(block)

// helper function to dump exception to stdout for ease of debugging failed tests
private inline fun <T> outputException(name: String, block: () -> T): T =
    try { block() }
    catch (e: Throwable) {
        println("--- Failed test$name")
        e.printStackTrace(System.out)
        throw e
    }

private const val SHUTDOWN_TIMEOUT = 5000L // 5 sec at most to wait
private val OUT_ENABLED = systemProp("guide.tests.sout", false)

@Suppress("DEPRECATION")
fun <R> test(name: String, block: () -> R): List<String> = outputException(name) {
    val sout = System.out
    val oldOut = if (OUT_ENABLED) System.out else NullOut
    val oldErr = System.err
    val bytesOut = ByteArrayOutputStream()
    val tee = TeeOutput(bytesOut, oldOut)
    val ps = PrintStream(tee)

    oldOut.println("--- Running test$name")
    System.setErr(ps)
    System.setOut(ps)
    CommonPool.usePrivatePool()
    DefaultScheduler.usePrivateScheduler()
    DefaultExecutor.shutdown(SHUTDOWN_TIMEOUT)
    resetCoroutineId()
    val threadsBefore = currentThreads()
    var bytes = ByteArray(0)
    withVirtualTimeSource(oldOut) {
        try {
            val result = block()
            require(result === Unit) { "Test 'main' shall return Unit" }
        } catch (e: Throwable) {
            System.err.print("Exception in thread \"main\" ")
            e.printStackTrace()
        } finally {
            // capture output
            bytes = bytesOut.toByteArray()
            oldOut.println("--- shutting down")
            // the shutdown
            CommonPool.shutdown(SHUTDOWN_TIMEOUT)
            DefaultScheduler.shutdown(SHUTDOWN_TIMEOUT)
            shutdownDispatcherPools(SHUTDOWN_TIMEOUT)
            DefaultExecutor.shutdown(SHUTDOWN_TIMEOUT) // the last man standing -- cleanup all pending tasks
            if (tee.flushLine()) oldOut.println()
            oldOut.println("--- done")
            System.setOut(sout)
            System.setErr(oldErr)
            checkTestThreads(threadsBefore)
        }
    }
    CommonPool.restore()
    DefaultScheduler.restore()
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


private fun shutdownDispatcherPools(timeout: Long) {
    val threads = arrayOfNulls<Thread>(Thread.activeCount())
    val n = Thread.enumerate(threads)
    for (i in 0 until n) {
        val thread = threads[i]
        if (thread is PoolThread)
            (thread.dispatcher.executor as ExecutorService).apply {
                shutdown()
                awaitTermination(timeout, TimeUnit.MILLISECONDS)
                shutdownNow().forEach { DefaultExecutor.enqueue(it) }
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
            res = res.replace(Regex("ForkJoinPool\\.commonPool-worker-[0-9]+"), "DefaultDispatcher")
            res = res.replace(Regex("ForkJoinPool-[0-9]+-worker-[0-9]+"), "DefaultDispatcher")
            res = res.replace(Regex("CommonPool-worker-[0-9]+"), "DefaultDispatcher")
            res = res.replace(Regex("DefaultDispatcher-worker-[0-9]+"), "DefaultDispatcher")
            res = res.replace(Regex("RxComputationThreadPool-[0-9]+"), "RxComputationThreadPool")
            res = res.replace(Regex("Test( worker)?"), "main")
            res = res.replace(Regex("@[0-9a-f]+"), "") // drop hex address
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
        assertEquals(exp, act, "Line ${i + 1}")
    }
}

private fun List<String>.checkEqualNumberOfLines(expected: Array<out String>) {
    if (size > expected.size)
        error("Expected ${expected.size} lines, but found $size. Unexpected line '${get(expected.size)}'")
    else if (size < expected.size)
        error("Expected ${expected.size} lines, but found $size")
}

fun List<String>.verifyLines(vararg expected: String) = verify {
    verifyCommonLines(expected)
    checkEqualNumberOfLines(expected)
}

fun List<String>.verifyLinesStartWith(vararg expected: String) = verify {
    verifyCommonLines(expected)
    assertTrue(expected.size <= size, "Number of lines")
}

fun List<String>.verifyLinesArbitraryTime(vararg expected: String) = verify {
    verifyCommonLines(expected, SanitizeMode.ARBITRARY_TIME)
    checkEqualNumberOfLines(expected)
}

fun List<String>.verifyLinesFlexibleThread(vararg expected: String) = verify {
    verifyCommonLines(expected, SanitizeMode.FLEXIBLE_THREAD)
    checkEqualNumberOfLines(expected)
}

fun List<String>.verifyLinesStartUnordered(vararg expected: String) = verify {
    val expectedSorted = expected.sorted().toTypedArray()
    sorted().verifyLinesStart(*expectedSorted)
}

fun List<String>.verifyExceptions(vararg expected: String) {
    val original = this
    val actual = ArrayList<String>().apply {
        var except = false
        for (line in original) {
            when {
                !except && line.startsWith("\tat") -> except = true
                except && !line.startsWith("\t") && !line.startsWith("Caused by: ") -> except = false
            }
            if (!except) add(line)
        }
    }
    val n = minOf(actual.size, expected.size)
    for (i in 0 until n) {
        val exp = sanitize(expected[i], SanitizeMode.FLEXIBLE_THREAD)
        val act = sanitize(actual[i], SanitizeMode.FLEXIBLE_THREAD)
        assertEquals(exp, act, "Line ${i + 1}")
    }
}


fun List<String>.verifyLinesStart(vararg expected: String) = verify {
    val n = minOf(size, expected.size)
    for (i in 0 until n) {
        val exp = sanitize(expected[i], SanitizeMode.FLEXIBLE_THREAD)
        val act = sanitize(get(i), SanitizeMode.FLEXIBLE_THREAD)
        assertEquals(exp, act.substring(0, minOf(act.length, exp.length)), "Line ${i + 1}")
    }
    checkEqualNumberOfLines(expected)
}

private object NullOut : PrintStream(NullOutputStream())

private class NullOutputStream : OutputStream() {
    override fun write(b: Int) = Unit
}

private inline fun List<String>.verify(verification: () -> Unit) {
    try {
        verification()
    } catch (t: Throwable) {
        if (!OUT_ENABLED) {
            println("Printing [delayed] test output")
            forEach { println(it) }
        }

        throw t
    }
}