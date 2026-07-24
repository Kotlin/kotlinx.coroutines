package kotlinx.coroutines

import java.util.concurrent.*
import java.util.concurrent.locks.LockSupport
import kotlin.coroutines.*

/** Base dispatcher for coroutines that own a virtual thread. */
internal abstract class VirtualThreadDispatcher : ExecutorCoroutineDispatcher() {
    private companion object {
        // Reflective so the library can still be compiled to its Java 8 bytecode target. The experiment
        // itself is exercised on JDK 25, where this method is guaranteed to exist.
        val executorService =
            Executors::class.java.getMethod("newVirtualThreadPerTaskExecutor").invoke(null) as ExecutorService
    }

    final override val executor: Executor
        get() = executorService

    final override fun dispatch(context: CoroutineContext, block: Runnable) {
        executorService.execute { runTask(block) }
    }

    protected open fun runTask(block: Runnable) {
        block.run()
    }

    internal open fun releaseForSuspension() {}

    internal open fun reacquireAfterSuspension() {}

    protected fun shutdown() {
        executorService.shutdown()
    }

    override fun close() {
        throw UnsupportedOperationException("Dispatchers.Default cannot be closed")
    }

}

/** The experimental default dispatcher: every dispatched continuation gets a fresh virtual thread. */
internal object DefaultVirtualThreadDispatcher : VirtualThreadDispatcher() {
    internal fun shutdownDefault() {
        shutdown()
    }

    override fun toString(): String = "Dispatchers.Default"
}

/** A virtual-thread dispatcher whose runnable segments are limited by a fair semaphore. */
internal class SemaphoreVirtualThreadDispatcher(parallelism: Int) : VirtualThreadDispatcher() {
    private val semaphore = Semaphore(parallelism, true)

    init {
        require(parallelism >= 1) { "Expected positive parallelism level, but got $parallelism" }
    }

    override fun runTask(block: Runnable) {
        semaphore.acquireUninterruptibly()
        try {
            block.run()
        } finally {
            semaphore.release()
        }
    }

    override fun releaseForSuspension() {
        semaphore.release()
    }

    override fun reacquireAfterSuspension() {
        semaphore.acquireUninterruptibly()
    }
}

internal actual class VirtualThreadWaiter actual constructor(context: CoroutineContext) {
    private val thread = Thread.currentThread()
    private val dispatcher = context[ContinuationInterceptor] as? VirtualThreadDispatcher

    actual fun await() {
        dispatcher?.releaseForSuspension()
        try {
            LockSupport.park(this)
        } finally {
            dispatcher?.reacquireAfterSuspension()
        }
    }

    actual fun signal() {
        LockSupport.unpark(thread)
    }
}
