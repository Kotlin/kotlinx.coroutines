/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.metrics

import com.codahale.metrics.InstrumentedExecutorService
import com.codahale.metrics.MetricRegistry
import kotlinx.coroutines.experimental.ExecutorCoroutineDispatcher
import kotlinx.coroutines.experimental.asCoroutineDispatcher
import kotlinx.coroutines.experimental.yield
import java.util.concurrent.Executors

/**
 * Creates a new instrumented coroutine execution context using a single thread with built-in [yield] support.
 * **NOTE: The resulting [ExecutorCoroutineDispatcher] owns native resources (its thread).
 * Resources are reclaimed by [ExecutorCoroutineDispatcher.close].**
 *
 * @param name the base name of the created thread.
 * @param metricRegistry MetricRegistry that will contain the metrics.
 */
fun newInstrumentedSingleThreadContext(name: String, metricRegistry: MetricRegistry): ExecutorCoroutineDispatcher =
        newInstrumentedFixedThreadPoolContext(1, name, metricRegistry)

/**
 * Creates new instrumented coroutine execution context with the fixed-size thread-pool and built-in [yield] support.
 * **NOTE: The resulting [ExecutorCoroutineDispatcher] owns native resources (its threads).
 * Resources are reclaimed by [ExecutorCoroutineDispatcher.close].**
 *
 * @param nThreads the number of threads.
 * @param name the base name of the created threads.
 * @param metricRegistry MetricRegistry that will contain the metrics.
 */
fun newInstrumentedFixedThreadPoolContext(nThreads: Int,
                                          name: String,
                                          metricRegistry: MetricRegistry): ExecutorCoroutineDispatcher =
        InstrumentedExecutorService(
                Executors.newScheduledThreadPool(nThreads)
                { runnable -> Thread(runnable, name) }, metricRegistry, name)
                .asCoroutineDispatcher()
