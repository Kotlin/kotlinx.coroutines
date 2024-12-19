@file:OptIn(ObsoleteWorkersApi::class)

package kotlinx.coroutines.scheduling

import kotlinx.atomicfu.*
import kotlinx.atomicfu.parking.KThread
import kotlinx.atomicfu.parking.Parker
import kotlinx.coroutines.internal.Symbol
import kotlinx.coroutines.nanoTime
import platform.posix.*
import kotlin.native.concurrent.*
import kotlin.time.*

internal actual fun ioParallelism(): Int = 64

internal actual abstract class MultiplatformThread private constructor(worker: KThread?) {

    internal actual constructor(isDaemon: Boolean, contextClassLoaderSource: Any) : this(null)

    private val name = atomic<String?>(null)
    private val worker = atomic<Any?>(worker)

    actual companion object {
        actual fun currentThread(): MultiplatformThread? = ExistingMultiplatformThread(KThread.currentThread())
    }

    // TODO: does not respect timeouts
    actual fun awaitTermination(timeout: Duration) {
        worker.compareAndSet(null, TERMINATED)
        val future: Future<Unit> = (worker.value as? Worker ?: return).requestTermination(processScheduledJobs = true)
        future.consume {
        }
    }

    actual fun unpark() {
        (worker.value as? KThread)?.let(Parker::unpark)
    }

    actual abstract fun run()

    actual fun start() {
        Worker.start(name = name.value).apply {
            executeAfter(0) {
                if (worker.compareAndSet(null, KThread.currentThread())) {
                    run()
                } else if (worker.value !== TERMINATED) {
                    error("This thread's task was already running")
                }
            }
        }
    }

    private class ExistingMultiplatformThread(worker: KThread) : MultiplatformThread(worker) {
        override fun run() {
            error("This thread's task is already running")
        }
    }

    // TODO: only works before the Worker is started
    actual fun setName(name: String) {
        this.name.value = name
    }

    actual fun clearInterruptFlag() {
        // no-op: no interrupts on native
    }

    actual fun reportException(exception: Throwable) {
        processUnhandledException(exception)
    }
}

private val TERMINATED = Symbol("TERMINATED")

internal actual fun parkNanosCurrentThread(timeNanos: Long) {
    Parker.parkNanos(timeNanos)
}

internal actual fun yieldThread() { sched_yield() }

internal actual fun actualNanoTime(): Long = nanoTime()

// force initialize the number of processors at startup for consistent prop initialization
internal actual val AVAILABLE_PROCESSORS = Platform.getAvailableProcessors()

internal actual fun trackTask() { }

internal actual fun unTrackTask() { }

internal actual class RejectedExecutionException actual constructor(message: String?) : Throwable(message)
