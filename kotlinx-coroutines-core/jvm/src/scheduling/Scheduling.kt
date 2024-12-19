package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import java.util.concurrent.locks.*
import kotlin.time.*

internal actual fun ioParallelism(): Int =
    systemProp(IO_PARALLELISM_PROPERTY_NAME, 64.coerceAtLeast(AVAILABLE_PROCESSORS))

internal actual abstract class MultiplatformThread internal actual constructor(
    isDaemon: Boolean, contextClassLoaderSource: Any
): Thread() {

    init {
        this.isDaemon = isDaemon
        /*
         * `Dispatchers.Default` is used as *the* dispatcher in the containerized environments,
         * isolated by their own classloaders. Workers are populated lazily, thus we are inheriting
         * `Dispatchers.Default` context class loader here instead of using parent' thread one
         * in order not to accidentally capture temporary application classloader.
         */
        this.contextClassLoader = contextClassLoaderSource.javaClass.classLoader
    }

    actual companion object {
        actual fun currentThread(): MultiplatformThread? = Thread.currentThread() as? MultiplatformThread
    }

    actual fun awaitTermination(timeout: Duration) {
        while (state != State.TERMINATED) {
            LockSupport.unpark(this)
            join(timeout.inWholeMilliseconds)
        }
    }

    actual fun unpark() {
        LockSupport.unpark(this)
    }

    actual abstract override fun run()

    actual fun clearInterruptFlag() {
        interrupted() // clear interrupt flag
    }

    actual fun reportException(exception: Throwable) {
        uncaughtExceptionHandler.uncaughtException(this, exception)
    }
}

internal actual fun parkNanosCurrentThread(timeNanos: Long) { LockSupport.parkNanos(timeNanos) }

internal actual fun yieldThread() { Thread.yield() }

internal actual fun actualNanoTime(): Long = System.nanoTime()

// force initialize the number of processors at startup for consistent prop initialization
internal actual val AVAILABLE_PROCESSORS = Runtime.getRuntime().availableProcessors()

internal actual fun trackTask() = kotlinx.coroutines.trackTask()

internal actual fun unTrackTask() = kotlinx.coroutines.unTrackTask()

internal actual typealias RejectedExecutionException = java.util.concurrent.RejectedExecutionException

/**
 * Checks if the thread is part of a thread pool that supports coroutines.
 * This function is needed for integration with BlockHound.
 */
@JvmName("isSchedulerWorker")
internal fun isSchedulerWorker(thread: Thread) = thread is CoroutineScheduler.Worker

/**
 * Checks if the thread is running a CPU-bound task.
 * This function is needed for integration with BlockHound.
 */
@JvmName("mayNotBlock")
internal fun mayNotBlock(thread: Thread) = thread is CoroutineScheduler.Worker &&
    thread.state == CoroutineScheduler.WorkerState.CPU_ACQUIRED
