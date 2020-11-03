/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.flow

import benchmarks.common.*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.TimeUnit

/**
 * Benchmark to measure performance of [kotlinx.coroutines.flow.FlowKt.flattenMerge].
 * In addition to that, it can be considered as a macro benchmark for the [kotlinx.coroutines.sync.Semaphore]
 */
@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 5, time = 1)
@BenchmarkMode(Mode.Throughput)
@OutputTimeUnit(TimeUnit.SECONDS)
@State(Scope.Benchmark)
@Fork(1)
open class FlowFlattenMergeBenchmark {
    @Param
    private var flowsNumberStrategy: FlowsNumberStrategy = FlowsNumberStrategy.`10xConcurrency flows`

    @Param("1", "2", "4", "8")
    private var concurrency: Int = 0

    private lateinit var flow: Flow<Flow<Int>>

    @Setup
    fun setup() {
        val n = flowsNumberStrategy.get(concurrency)
        val flowElementsToProcess = ELEMENTS / n

        flow = (1..n).asFlow().map {
            flow {
                repeat(flowElementsToProcess) {
                    doGeomDistrWork(WORK)
                    emit(it)
                }
            }
        }
    }

    @Benchmark
    fun flattenMerge() = runBlocking(Dispatchers.Default) {
        flow.flattenMerge(concurrency = concurrency).collect()
    }
}

enum class FlowsNumberStrategy(val get: (concurrency: Int) -> Int) {
    `10xConcurrency flows`({ concurrency -> concurrency * 10 }),
    `1xConcurrency flows`({ it }),
    `100 flows`({ 100 }),
    `500 flows`({ 500 })
}

// If you change this variable please be sure that you change variable elements in the generate_plots_flow_flatten_merge.py
// python script as well
private const val ELEMENTS = 100_000
private const val WORK = 100
