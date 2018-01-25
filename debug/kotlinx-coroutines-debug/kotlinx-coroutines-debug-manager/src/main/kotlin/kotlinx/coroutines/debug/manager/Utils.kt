package kotlinx.coroutines.debug.manager

import java.io.PrintWriter
import java.io.StringWriter

fun Any?.toStringSafe() = try {
    toString()
} catch (e: Throwable) {
    "<can't be printed ($e)>"
}

fun Throwable.stackTraceToString(): String {
    val writer = StringWriter()
    printStackTrace(PrintWriter(writer))
    return writer.toString()
}

val PROPERTY_ENABLE_DEBUG = "coroutines.debug.enabled"
val PROPERTY_DEBUG_LOG_LEVEL = "coroutines.debug.logLevel"

val ALL_SUSPEND_CALLS_DUMP_FILE_NAME = "all-suspend-calls.dump"
val KNOWND_DORESUME_FUNCTIONS_DUMP_FILE_NAME = "known-doResume-functions.dump"