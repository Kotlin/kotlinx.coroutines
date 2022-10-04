/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines // Trick to make guide tests use these declarations with executors that can be closed on our side implicitly

import java.util.concurrent.*
import java.util.concurrent.atomic.*
import kotlin.coroutines.*

internal fun newSingleThreadContext(name: String): ExecutorCoroutineDispatcher = ClosedAfterGuideTestDispatcher(1, name)

internal fun newFixedThreadPoolContext(nThreads: Int, name: String): ExecutorCoroutineDispatcher =
    ClosedAfterGuideTestDispatcher(nThreads, name)

internal class PoolThread(
    @JvmField val dispatcher: ExecutorCoroutineDispatcher, // for debugging & tests
    target: Runnable, name: String
) : Thread(target, name) {
    init {
        isDaemon = true
    }
}

private class ClosedAfterGuideTestDispatcher(
    private val nThreads: Int,
    private val name: String
) : ExecutorCoroutineDispatcher() {
    private val threadNo = AtomicInteger()

    override val executor: Executor =
        Executors.newScheduledThreadPool(nThreads, object : ThreadFactory {
            override fun newThread(target: java.lang.Runnable): Thread {
                return PoolThread(
                    this@ClosedAfterGuideTestDispatcher,
                    target,
                    if (nThreads == 1) name else name + "-" + threadNo.incrementAndGet()
                )
            }
        })

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        executor.execute(wrapTask(block))
    }

    override fun close() {
        (executor as ExecutorService).shutdown()
    }

    override fun toString(): String = "ThreadPoolDispatcher[$nThreads, $name]"
}
