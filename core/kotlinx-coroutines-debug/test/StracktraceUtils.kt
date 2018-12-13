/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug

import java.io.*
import kotlin.test.*

public fun String.trimStackTrace(): String =
    trimIndent()
        .replace(Regex(":[0-9]+"), "")
        .replace(Regex("#[0-9]+"), "")
        .applyBackspace()

public fun String.applyBackspace(): String {
    val array = toCharArray()
    val stack = CharArray(array.size)
    var stackSize = -1
    for (c in array) {
        if (c != '\b') {
            stack[++stackSize] = c
        } else {
            --stackSize
        }
    }

    return String(stack, 0, stackSize + 1)
}

public fun verifyStackTrace(e: Throwable, traces: List<String>) {
    val stacktrace = toStackTrace(e)
    traces.forEach {
        val expectedLines = it.trimStackTrace().split("\n")
        for (i in 0 until expectedLines.size) {
            traces.forEach {
                assertTrue(
                    stacktrace.trimStackTrace().contains(it.trimStackTrace()),
                    "\nExpected trace element:\n$it\n\nActual stacktrace:\n$stacktrace"
                )
            }
        }
    }

    val causes = stacktrace.count("Caused by")
    assertNotEquals(0, causes)
    assertEquals(causes, traces.map { it.count("Caused by") }.sum())
}

public fun toStackTrace(t: Throwable): String {
    val sw = StringWriter()
    t.printStackTrace(PrintWriter(sw))
    return sw.toString()
}

public fun String.count(substring: String): Int = split(substring).size - 1

public fun verifyDump(vararg traces: String) {
    val baos = ByteArrayOutputStream()
    DebugProbes.dumpCoroutines(PrintStream(baos))
    val trace = baos.toString().split("\n\n")
    if (traces.isEmpty()) {
        assertEquals(1, trace.size)
        assertTrue(trace[0].startsWith("Coroutines dump"))
        return
    }
    // Drop "Coroutine dump" line
    trace.withIndex().drop(1).forEach { (index, value) ->
        val expected = traces[index - 1].applyBackspace().split("\n\t(Coroutine creation stacktrace)\n", limit = 2)
        val actual = value.applyBackspace().split("\n\t(Coroutine creation stacktrace)\n", limit = 2)
        assertEquals(expected.size, actual.size)

        expected.withIndex().forEach { (index, trace) ->
            val actualTrace = actual[index].trimStackTrace().sanitizeAddresses()
            val expectedTrace = trace.trimStackTrace().sanitizeAddresses()
            val actualLines = actualTrace.split("\n")
            val expectedLines = expectedTrace.split("\n")
            for (i in 0 until expectedLines.size) {
                assertEquals(expectedLines[i], actualLines[i])
            }
        }
    }
}

public fun String.trimPackage() = replace("kotlinx.coroutines.debug.", "")

public fun verifyPartialDump(createdCoroutinesCount: Int, vararg frames: String) {
    val baos = ByteArrayOutputStream()
    DebugProbes.dumpCoroutines(PrintStream(baos))
    val dump = baos.toString()
    val trace = dump.split("\n\n")
    val matches = frames.all { frame ->
        trace.any { tr -> tr.contains(frame) }
    }

    assertEquals(createdCoroutinesCount, DebugProbes.dumpCoroutinesState().size)
    assertTrue(matches)
}

private fun String.sanitizeAddresses(): String {
    val index = indexOf("coroutine\"")
    val next = indexOf(',', index)
    if (index == -1 || next == -1) return this
    return substring(0, index) + substring(next, length)
}
