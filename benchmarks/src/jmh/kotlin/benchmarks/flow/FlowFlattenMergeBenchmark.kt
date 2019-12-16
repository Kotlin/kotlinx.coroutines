/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package benchmarks.flow

import benchmarks.common.*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*

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

    /**
     * Number of flows that are merged in this benchmark. Negative number means that number of flows
     * will be computed as -([flows] * [concurrency]), positive number will be chosen as number of flows.
     */
    @Param
    private var flows: Flows = Flows.`10xConcurrency flows`

    @Param("1", "2", "4")
    private var concurrency: Int = 0

    private lateinit var flow: Flow<Flow<Int>>

    @Setup
    fun setup() {
        val n = flows.getFlows(concurrency)
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

enum class Flows {
    `10xConcurrency flows` {
        override fun getFlows(concurrency: Int): Int = 10 * concurrency
    },
    `1xConcurrency flows` {
        override fun getFlows(concurrency: Int): Int = concurrency
    },
    `100 flows` {
        override fun getFlows(concurrency: Int): Int = 100
    },
    `500 flows` {
        override fun getFlows(concurrency: Int): Int = 500
    };

    abstract fun getFlows(concurrency : Int): Int
}

// If you change this variable please be sure that you change variable elements in the generate_plots_flow_flatten_merge.py
// python script as well
private const val ELEMENTS = 100_000
private const val WORK = 100