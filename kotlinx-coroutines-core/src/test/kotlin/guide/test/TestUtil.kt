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
import java.io.PrintStream
import java.util.concurrent.TimeUnit

fun test(name: String, block: () -> Unit): List<String> {
    println("--- Running test$name")
    val oldOut = System.out
    val oldErr = System.err
    val bytesOut = ByteArrayOutputStream()
    val ps = PrintStream(bytesOut)
    System.setErr(ps)
    System.setOut(ps)
    CommonPool.usePrivatePool()
    resetCoroutineId()
    var bytes: ByteArray
    try {
        block()
    } catch (e: Throwable) {
        System.err.print("Exception in thread \"main\" ")
        e.printStackTrace()
    } finally {
        // capture output
        bytes = bytesOut.toByteArray()
        // the shutdown
        val timeout = 5000L // 5 sec at most to wait
        CommonPool.shutdown(timeout)
        shutdownDispatcherPools(timeout)
        shutdownDefaultExecutor(timeout) // the last man standing -- kill it too
        CommonPool.restore()
        System.setOut(oldOut)
        System.setErr(oldErr)

    }
    val lines = ByteArrayInputStream(bytes).bufferedReader().readLines()
    lines.forEach {
        val limit = 80
        if (it.length < limit)
            println(it)
        else
            println(it.substring(0, limit) + " (${it.length} chars)")
    }
    return lines
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
                shutdownNow().forEach { defaultExecutor.execute(it) }
            }
    }
}

enum class SanitizeMode {
    NONE,
    ARBITRARY_TIME,
    FLEXIBLE_TIME,
    FLEXIBLE_THREAD
}

private fun sanitize(s: String, mode: SanitizeMode): String {
    var res = s
    when (mode) {
        SanitizeMode.ARBITRARY_TIME -> {
            res = res.replace(Regex(" [0-9]+ ms"), " xxx ms")
        }
        SanitizeMode.FLEXIBLE_TIME -> {
            res = res.replace(Regex("[0-9][0-9][0-9] ms"), "xxx ms")
        }
        SanitizeMode.FLEXIBLE_THREAD -> {
            res = res.replace(Regex("ForkJoinPool\\.commonPool-worker-[0-9]+"), "CommonPool")
            res = res.replace(Regex("ForkJoinPool-[0-9]+-worker-[0-9]+"), "CommonPool")
            res = res.replace(Regex("CommonPool-worker-[0-9]+"), "CommonPool")
            res = res.replace(Regex("RxComputationThreadPool-[0-9]+"), "RxComputationThreadPool")
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

fun List<String>.verifyLinesFlexibleTime(vararg expected: String) {
    verifyCommonLines(expected, SanitizeMode.FLEXIBLE_TIME)
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