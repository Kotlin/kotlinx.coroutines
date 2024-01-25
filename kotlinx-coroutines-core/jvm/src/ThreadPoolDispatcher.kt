@file:JvmMultifileClass
@file:JvmName("ThreadPoolDispatcherKt")
package kotlinx.coroutines

import java.util.concurrent.*
import java.util.concurrent.atomic.AtomicInteger

@DelicateCoroutinesApi
public actual fun newFixedThreadPoolContext(nThreads: Int, name: String): ExecutorCoroutineDispatcher {
    require(nThreads >= 1) { "Expected at least one thread, but $nThreads specified" }
    val threadNo = AtomicInteger()
    val executor = Executors.newScheduledThreadPool(nThreads) { runnable ->
        val t = Thread(runnable, if (nThreads == 1) name else name + "-" + threadNo.incrementAndGet())
        t.isDaemon = true
        t
    }
    return executor.asCoroutineDispatcher()
}
