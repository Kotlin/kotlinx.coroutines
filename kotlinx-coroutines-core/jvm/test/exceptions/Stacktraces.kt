package kotlinx.coroutines.exceptions

import java.io.*
import kotlin.test.*

public fun verifyStackTrace(e: Throwable, vararg traces: String) {
    val stacktrace = toStackTrace(e)
    traces.forEach {
        assertTrue(
            stacktrace.trimStackTrace().contains(it.trimStackTrace()),
            "\nExpected trace element:\n$it\n\nActual stacktrace:\n$stacktrace"
        )
    }

    val causes = stacktrace.count("Caused by")
    assertNotEquals(0, causes)
    assertEquals(traces.map { it.count("Caused by") }.sum(), causes)
}

public fun toStackTrace(t: Throwable): String {
    val sw = StringWriter() as Writer
    t.printStackTrace(PrintWriter(sw))
    return sw.toString()
}

public fun String.trimStackTrace(): String {
    return applyBackspace(trimIndent().replace(Regex(":[0-9]+"), "")
        .replace("kotlinx_coroutines_core_main", "") // yay source sets
        .replace("kotlinx_coroutines_core", ""))
}

public fun applyBackspace(line: String): String {
    val array = line.toCharArray()
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