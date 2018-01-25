package kotlinx.coroutines.debug.manager

import java.io.FileOutputStream
import java.io.OutputStream
import java.io.PrintWriter
import java.text.SimpleDateFormat
import java.util.*

inline fun debug(msg: () -> Any?) = message(LogLevel.DEBUG, msg)

inline fun info(msg: () -> Any?) = message(LogLevel.INFO, msg)
inline fun error(msg: () -> Any?) = message(LogLevel.ERROR, msg)

inline fun data(msg: () -> Any?) = Logger.config.doData(msg.toStringSafe())

enum class LogLevel {
    DEBUG, INFO, ERROR
}

data class LogConsumer(val level: LogLevel, val consumerWriter: PrintWriter) {
    constructor(level: LogLevel, consumerStream: OutputStream) : this(level, PrintWriter(consumerStream, true))
}

fun logToFile(
        level: LogLevel,
        name: String = "",
        withTime: Boolean = false,
        logFileOutputStream: FileOutputStream,
        dataConsumers: List<OutputStream> = emptyList()
): LoggerConfig {
    val logConsumer = LogConsumer(level, logFileOutputStream)
    return LoggerConfig(level, name, withTime, listOf(logConsumer), dataConsumers)
}

class LoggerConfig(
        val level: LogLevel,
        val name: String = "",
        val withTime: Boolean = false,
        val consumers: List<LogConsumer> = listOf(LogConsumer(LogLevel.DEBUG, System.err)),
        dataConsumers: List<OutputStream> = listOf(System.err)
) {
    val dataConsumers = dataConsumers.toHashSet().map { PrintWriter(it, true) }
}

object Logger {
    @Volatile
    var config: LoggerConfig = LoggerConfig(LogLevel.INFO)
}

inline fun message(withLevel: LogLevel, msg: () -> Any?) {
    val config = Logger.config
    if (withLevel >= config.level) {
        config.doLog(withLevel, build(msg))
    }
}

@PublishedApi
internal fun LoggerConfig.doData(msg: String) {
    val text = "${currentTimePretty()}:\n$msg"
    dataConsumers.forEach { it.println(text) }
}

@PublishedApi
internal fun LoggerConfig.doLog(withLevel: LogLevel, msg: String) {
    val text = "${withLevel.name} $msg"
    consumers.filter { withLevel >= it.level }.forEach { it.consumerWriter.println(text) }
}

@PublishedApi
internal inline fun build(msg: () -> Any?) = "${prefix()}: ${msg.toStringSafe()}"

@PublishedApi
internal fun prefix() = buildString {
    if (Logger.config.withTime) append("[${currentTimePretty()}] ") else append("")
    if (Logger.config.name.isNotEmpty()) append("${Logger.config.name}:") else append("")
}

@Suppress("NOTHING_TO_INLINE")
@PublishedApi
internal inline fun (() -> Any?).toStringSafe() =
        try {
            invoke().toString()
        } catch (e: Exception) {
            "Log message invocation failed: $e"
        }

fun currentTimePretty(pattern: String = "dd.MM.yyyy HH:mm:ss.SSS"): String =
        SimpleDateFormat(pattern).format(Date(System.currentTimeMillis()))
