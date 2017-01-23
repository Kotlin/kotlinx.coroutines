package kotlinx.coroutines.experimental

import java.util.concurrent.Executor
import java.util.concurrent.Executors
import java.util.concurrent.ForkJoinPool
import java.util.concurrent.atomic.AtomicInteger
import kotlin.coroutines.CoroutineContext

/**
 * Represents common pool of shared threads as coroutine dispatcher for compute-intensive tasks.
 * It uses [ForkJoinPool] when available, which implements efficient work-stealing algorithm for its queues, so every
 * coroutine resumption is dispatched as a separate task even when it already executes inside the pool.
 * When available, it wraps [ForkJoinPool.commonPool] and provides a similar shared pool where not.
 */
object CommonPool : CoroutineDispatcher() {
    private val pool: Executor = findPool()

    private inline fun <T> Try(block: () -> T) = try { block() } catch (e: Throwable) { null }

    private fun findPool(): Executor {
        val fjpClass = Try { Class.forName("java.util.concurrent.ForkJoinPool") }
            ?: return createPlainPool()
        Try { fjpClass.getMethod("commonPool")?.invoke(null) as? Executor }
            ?. let { return it }
        Try { fjpClass.getConstructor(Int::class.java).newInstance(defaultParallelism()) as? Executor }
            ?. let { return it }
        return createPlainPool()
    }

    private fun createPlainPool(): Executor {
        val threadId = AtomicInteger()
        return Executors.newFixedThreadPool(defaultParallelism()) {
            Thread(it, "CommonPool-worker-${threadId.incrementAndGet()}").apply { isDaemon = true }
        }
    }

    private fun defaultParallelism() = (Runtime.getRuntime().availableProcessors() - 1).coerceAtLeast(1)

    override fun isDispatchNeeded(context: CoroutineContext): Boolean = true
    override fun dispatch(context: CoroutineContext, block: Runnable) = pool.execute(block)
}
