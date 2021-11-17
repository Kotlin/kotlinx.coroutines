/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug

import java.io.*
import kotlin.test.*

public fun String.trimStackTrace(): String =
    trimIndent()
        .replace(Regex(":[0-9]+"), "")
        .replace(Regex("#[0-9]+"), "")
        .replace(Regex("(?<=\tat )[^\n]*/"), "")
        .replace(Regex("\t"), "")
        .replace("sun.misc.Unsafe.", "jdk.internal.misc.Unsafe.") // JDK8->JDK11
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
    val trimmedStackTrace = stacktrace.trimStackTrace()
    traces.forEach {
        assertTrue(
            trimmedStackTrace.contains(it.trimStackTrace()),
            "\nExpected trace element:\n$it\n\nActual stacktrace:\n$stacktrace"
        )
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

public fun verifyDump(vararg traces: String, ignoredCoroutine: String? = null, finally: () -> Unit) {
    try {
        verifyDump(*traces, ignoredCoroutine = ignoredCoroutine)
    } finally {
        finally()
    }
}

/** Clean the stacktraces from artifacts of BlockHound instrumentation
 *
 * BlockHound works by switching a native call by a class generated with ByteBuddy, which, if the blocking
 * call is allowed in this context, in turn calls the real native call that is now available under a
 * different name.
 *
 * The traces thus undergo the following two changes when the execution is instrumented:
 *   - The original native call is replaced with a non-native one with the same FQN, and
 *   - An additional native call is placed on top of the stack, with the original name that also has
 *     `$$BlockHound$$_` prepended at the last component.
 */
private fun cleanBlockHoundTraces(frames: List<String>): List<String> {
    var result = mutableListOf<String>()
    val blockHoundSubstr = "\$\$BlockHound\$\$_"
    var i = 0
    while (i < frames.size) {
        result.add(frames[i].replace(blockHoundSubstr, ""))
        if (frames[i].contains(blockHoundSubstr)) {
            i += 1
        }
        i += 1
    }
    return result
}

public fun verifyDump(vararg traces: String, ignoredCoroutine: String? = null) {
    val baos = ByteArrayOutputStream()
    DebugProbes.dumpCoroutines(PrintStream(baos))
    val wholeDump = baos.toString()
    val trace = wholeDump.split("\n\n")
    if (traces.isEmpty()) {
        val filtered = trace.filter { ignoredCoroutine == null || !it.contains(ignoredCoroutine) }
        assertEquals(1, filtered.count())
        assertTrue(filtered[0].startsWith("Coroutines dump"))
        return
    }
    // Drop "Coroutine dump" line
    trace.withIndex().drop(1).forEach { (index, value) ->
        if (ignoredCoroutine != null && value.contains(ignoredCoroutine)) {
            return@forEach
        }

        val expected = traces[index - 1].applyBackspace().split("\n\t(Coroutine creation stacktrace)\n", limit = 2)
        val actual = value.applyBackspace().split("\n\t(Coroutine creation stacktrace)\n", limit = 2)
        assertEquals(expected.size, actual.size, "Creation stacktrace should be part of the expected input. Whole dump:\n$wholeDump")

        expected.withIndex().forEach { (index, trace) ->
            val actualTrace = actual[index].trimStackTrace().sanitizeAddresses()
            val expectedTrace = trace.trimStackTrace().sanitizeAddresses()
            val actualLines = cleanBlockHoundTraces(actualTrace.split("\n"))
            val expectedLines = expectedTrace.split("\n")
            for (i in expectedLines.indices) {
                assertEquals(expectedLines[i], actualLines[i], "Whole dump:\n$wholeDump")
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

    assertEquals(createdCoroutinesCount, DebugProbes.dumpCoroutinesInfo().size)
    assertTrue(matches)
}

private fun String.sanitizeAddresses(): String {
    val index = indexOf("coroutine\"")
    val next = indexOf(',', index)
    if (index == -1 || next == -1) return this
    return substring(0, index) + substring(next, length)
}
