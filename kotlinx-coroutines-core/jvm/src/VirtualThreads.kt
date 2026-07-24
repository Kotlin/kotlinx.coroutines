package kotlinx.coroutines

import java.util.concurrent.*
import java.util.concurrent.locks.LockSupport
import kotlin.coroutines.*

/** The experimental default dispatcher: every dispatched continuation gets a fresh virtual thread. */
internal object VirtualThreadDispatcher : ExecutorCoroutineDispatcher(), BlockingContinuationSupport {
    // Reflective so the library can still be compiled to its Java 8 bytecode target. The experiment
    // itself is exercised on JDK 25, where this method is guaranteed to exist.
    private val virtualThreadExecutor =
        Executors::class.java.getMethod("newVirtualThreadPerTaskExecutor").invoke(null) as ExecutorService

    override val executor: Executor
        get() = virtualThreadExecutor

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        virtualThreadExecutor.execute(block)
    }

    override fun createBlockingWaiter(): BlockingContinuationWaiter =
        VirtualThreadWaiter(Thread.currentThread())

    internal fun shutdown() {
        virtualThreadExecutor.shutdown()
    }

    override fun close() {
        throw UnsupportedOperationException("Dispatchers.Default cannot be closed")
    }

    override fun toString(): String = "Dispatchers.Default"
}

internal class VirtualThreadWaiter(private val thread: Thread) : BlockingContinuationWaiter {
    override fun await() {
        LockSupport.park(this)
    }

    override fun signal() {
        LockSupport.unpark(thread)
    }
}
