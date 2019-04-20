package kotlinx.coroutines.exceptions

import java.io.*
import kotlin.test.*

public fun verifyStackTrace(e: Throwable, vararg traces: String) {
    val stacktrace = toStackTrace(e)
    val normalizedActual = stacktrace.normalizeStackTrace()
    traces.forEach {
        val normalizedExpected = it.normalizeStackTrace()
        if (!normalizedActual.contains(normalizedExpected)) {
            // A more readable error message would be produced by assertEquals
            assertEquals(normalizedExpected, normalizedActual, "Actual trace does not contain expected one")
        }
    }
    // Check "Caused by" counts
    val causes = stacktrace.count("Caused by")
    assertNotEquals(0, causes)
    assertEquals(traces.map { it.count("Caused by") }.sum(), causes)
}

public fun toStackTrace(t: Throwable): String {
    val sw = StringWriter() as Writer
    t.printStackTrace(PrintWriter(sw))
    return sw.toString()
}

public fun String.normalizeStackTrace(): String =
    applyBackspace()
    .replace(Regex(":[0-9]+"), "") // remove line numbers
    .replace("kotlinx_coroutines_core_main", "") // yay source sets
    .replace("kotlinx_coroutines_core", "")
    .replace(Regex("@[0-9a-f]+"), "") // remove hex addresses in debug toStrings
    .lines().joinToString("\n") // normalize line separators

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
    return String(stack, 0, stackSize)
}

public fun String.count(substring: String): Int = split(substring).size - 1