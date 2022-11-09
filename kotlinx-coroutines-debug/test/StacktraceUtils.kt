/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug

import java.io.*
import kotlin.test.*

public fun String.trimStackTrace(): String =
    trimIndent()
        // Remove source line
        .replace(Regex(":[0-9]+"), "")
        // Remove coroutine id
        .replace(Regex("#[0-9]+"), "")
        // Remove trace prefix: "java.base@11.0.16.1/java.lang.Thread.sleep" => "java.lang.Thread.sleep"
        .replace(Regex("(?<=\tat )[^\n]*/"), "")
        .replace(Regex("\t"), "")
        .replace("sun.misc.Unsafe.", "jdk.internal.misc.Unsafe.") // JDK8->JDK11

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
    val result = mutableListOf<String>()
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

private data class CoroutineDump(
    val header: CoroutineDumpHeader,
    val coroutineStackTrace: List<String>,
    val threadStackTrace: List<String>,
    val originDump: String,
    val originHeader: String,
) {
    companion object {
        private val COROUTINE_CREATION_FRAME_REGEX =
            "at _COROUTINE\\._CREATION\\._\\(.*\\)".toRegex()

        fun parse(dump: String, traceCleaner: ((List<String>) -> List<String>)? = null): CoroutineDump {
            val lines = dump
                .trimStackTrace()
                .split("\n")
            val header = CoroutineDumpHeader.parse(lines[0])
            val traceLines = lines.slice(1 until lines.size)
            val cleanedTraceLines = if (traceCleaner != null) {
                traceCleaner(traceLines)
            } else {
                traceLines
            }
            val coroutineStackTrace = mutableListOf<String>()
            val threadStackTrace = mutableListOf<String>()
            var trace = coroutineStackTrace
            for (line in cleanedTraceLines) {
                if (line.isEmpty()) {
                    continue
                }
                if (line.matches(COROUTINE_CREATION_FRAME_REGEX)) {
                    require(trace !== threadStackTrace) {
                        "Found more than one coroutine creation frame"
                    }
                    trace = threadStackTrace
                    continue
                }
                trace.add(line)
            }
            return CoroutineDump(header, coroutineStackTrace, threadStackTrace, dump, lines[0])
        }
    }

    fun verify(expected: CoroutineDump) {
        assertEquals(
            expected.header, header,
            "Coroutine stacktrace headers are not matched:\n\t- ${expected.originHeader}\n\t+ ${originHeader}\n"
        )
        verifyStackTrace("coroutine stack", coroutineStackTrace, expected.coroutineStackTrace)
        verifyStackTrace("thread stack", threadStackTrace, expected.threadStackTrace)
    }

    private fun verifyStackTrace(traceName: String, actualStackTrace: List<String>, expectedStackTrace: List<String>) {
        // It is possible there are more stack frames in a dump than we check
        for ((ix, expectedLine) in expectedStackTrace.withIndex()) {
            val actualLine = actualStackTrace[ix]
            assertEquals(
                expectedLine, actualLine,
                "Following lines from $traceName are not matched:\n\t- ${expectedLine}\n\t+ ${actualLine}\nActual dump:\n$originDump\n\n"
            )
        }
    }
}

private data class CoroutineDumpHeader(
    val name: String?,
    val className: String,
    val state: String,
) {
    companion object {
        /**
         * Parses following strings:
         *
         * - Coroutine "coroutine#10":DeferredCoroutine{Active}@66d87651, state: RUNNING
         * - Coroutine DeferredCoroutine{Active}@66d87651, state: RUNNING
         *
         * into:
         *
         * - `CoroutineDumpHeader(name = "coroutine", className = "DeferredCoroutine", state = "RUNNING")`
         * - `CoroutineDumpHeader(name = null, className = "DeferredCoroutine", state = "RUNNING")`
         */
        fun parse(header: String): CoroutineDumpHeader {
            val (identFull, stateFull) = header.split(", ", limit = 2)
            val nameAndClassName = identFull.removePrefix("Coroutine ").split('@', limit = 2)[0]
            val (name, className) = nameAndClassName.split(':', limit = 2).let { parts ->
                val (quotedName, classNameWithState) = if (parts.size == 1) {
                    null to parts[0]
                } else {
                    parts[0] to parts[1]
                }
                val name = quotedName?.removeSurrounding("\"")?.split('#', limit = 2)?.get(0)
                val className = classNameWithState.replace("\\{.*\\}".toRegex(), "")
                name to className
            }
            val state = stateFull.removePrefix("state: ")
            return CoroutineDumpHeader(name, className, state)
        }
    }
}

public fun verifyDump(vararg expectedTraces: String, ignoredCoroutine: String? = null) {
    val baos = ByteArrayOutputStream()
    DebugProbes.dumpCoroutines(PrintStream(baos))
    val wholeDump = baos.toString()
    val traces = wholeDump.split("\n\n")
    assertTrue(traces[0].startsWith("Coroutines dump"))

    val dumps = traces
        // Drop "Coroutine dump" line
        .drop(1)
        // Parse dumps and filter out ignored coroutines
        .mapNotNull { trace ->
            val dump = CoroutineDump.parse(trace, traceCleaner = ::cleanBlockHoundTraces)
            if (dump.header.className == ignoredCoroutine) {
                null
            } else {
                dump
            }
        }

    assertEquals(expectedTraces.size, dumps.size)
    dumps.zip(expectedTraces.map(CoroutineDump::parse)).forEach { (dump, expectedDump) ->
        dump.verify(expectedDump)
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
