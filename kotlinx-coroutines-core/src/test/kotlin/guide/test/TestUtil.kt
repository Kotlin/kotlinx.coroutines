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

fun test(block: () -> Unit): List<String> {
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
        scheduledExecutorShutdownNow()
        shutdownDispatcherPools()
        CommonPool.shutdownAndRelease(10000L) // wait at most 10 sec
        scheduledExecutorShutdownNowAndRelease()
        System.setOut(oldOut)
        System.setErr(oldErr)

    }
    return ByteArrayInputStream(bytes).bufferedReader().readLines()
}

private fun shutdownDispatcherPools() {
    val threads = arrayOfNulls<Thread>(Thread.activeCount())
    val n = Thread.enumerate(threads)
    for (i in 0 until n) {
        val thread = threads[i]
        if (thread is PoolThread)
            thread.dispatcher.executor.shutdownNow()
    }
}

private fun sanitize(s: String, flexibleTime: Boolean = false, flexibleThread: Boolean = false): String {
    var res = s
    if (flexibleTime) {
        res = res.replace(Regex("[0-9][0-9][0-9] ms"), "xxx ms")
    }
    if (flexibleThread) {
        res = res.replace(Regex("ForkJoinPool\\.commonPool-worker-[0-9]+"), "CommonPool")
        res = res.replace(Regex("ForkJoinPool-[0-9]+-worker-[0-9]+"), "CommonPool")
        res = res.replace(Regex("CommonPool-worker-[0-9]+"), "CommonPool")
    }
    return res
}

private fun List<String>.verifyCommonLines(
    expected: Array<out String>,
    flexibleTime: Boolean = false,
    flexibleThread: Boolean = false
) {
    val n = minOf(size, expected.size)
    for (i in 0 until n) {
        val exp = sanitize(expected[i], flexibleTime = flexibleTime, flexibleThread = flexibleThread)
        val act = sanitize(get(i), flexibleTime = flexibleTime, flexibleThread = flexibleThread)
        assertEquals("Line ${i + 1}", exp, act)
    }
}

fun List<String>.verifyLines(vararg expected: String) {
    verifyCommonLines(expected)
    assertEquals("Number of lines", expected.size, size)
}

fun List<String>.verifyLinesStartWith(vararg expected: String) {
    verifyCommonLines(expected)
    assertTrue("Number of lines", expected.size <= size)
}

fun List<String>.verifyLinesFlexibleTime(vararg expected: String) {
    verifyCommonLines(expected, flexibleTime = true)
    assertEquals("Number of lines", expected.size, size)
}

fun List<String>.verifyLinesFlexibleThread(vararg expected: String) {
    verifyCommonLines(expected, flexibleThread = true)
    assertEquals("Number of lines", expected.size, size)
}

fun List<String>.verifyLinesStartUnordered(vararg expected: String) {
    val expectedSorted = expected.sorted().toTypedArray()
    sorted().verifyLinesStart(*expectedSorted)
}

fun List<String>.verifyLinesStart(vararg expected: String) {
    val n = minOf(size, expected.size)
    for (i in 0 until n) {
        val exp = sanitize(expected[i], flexibleThread = true)
        val act = sanitize(get(i), flexibleThread = true)
        assertEquals("Line ${i + 1}", exp, act.substring(0, minOf(act.length, exp.length)))
    }
    assertEquals("Number of lines", expected.size, size)
}