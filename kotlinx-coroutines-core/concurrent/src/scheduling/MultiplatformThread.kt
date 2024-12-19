package kotlinx.coroutines.scheduling

import kotlin.time.*

internal expect abstract class MultiplatformThread internal constructor(
    isDaemon: Boolean, contextClassLoaderSource: Any
) {
    companion object {
        fun currentThread(): MultiplatformThread?
    }

    fun awaitTermination(timeout: Duration)

    fun unpark()

    fun start()

    abstract fun run()

    fun setName(name: String)

    fun clearInterruptFlag()

    fun reportException(exception: Throwable)
}

internal expect fun parkNanosCurrentThread(timeNanos: Long)

internal expect fun ioParallelism(): Int

internal expect fun yieldThread()

internal expect fun actualNanoTime(): Long

internal expect val AVAILABLE_PROCESSORS: Int

internal expect fun trackTask()

internal expect fun unTrackTask()

internal expect class RejectedExecutionException(message: String?): Throwable
