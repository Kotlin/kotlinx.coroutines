/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package benchmarks.flow

import doGeomDistrWork
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.runBlocking
import org.openjdk.jmh.annotations.*
import java.util.concurrent.TimeUnit

/**
 * Benchmark to measure performance of [kotlinx.coroutines.flow.FlowKt.flattenMerge].
 * In addition to that, it can be considered as a macro benchmark for the [kotlinx.coroutines.sync.Semaphore]
 */
@Warmup(iterations = 3, time = 1)
@Measurement(iterations = 10, time = 1)
@BenchmarkMode(Mode.Throughput)
@OutputTimeUnit(TimeUnit.SECONDS)
@State(Scope.Benchmark)
@Fork(1)
open class FlowFlattenMergeBenchmark {

    /**
     * Number of flows that are merged in this benchmark. Negative number means that number of flows
     * will be computed as -([flows] * [concurrency]), positive number will be chosen as number of flows.
     */
    @Param("-10", "-1", "100", "500")
    private var flows: Int = 0

    @Param("1", "2", "4") // local machine
//    @Param("1", "2", "4", "8", "16", "32", "64", "96") // Google Cloud
    private var concurrency: Int = 0

    private lateinit var flow: Flow<Flow<Int>>

    @Setup
    fun setup() {
        val n = if (flows >= 0) flows else -(flows * concurrency)
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

// If you change this variable please be sure that you change variable elements in the corresponding python script as well
private const val ELEMENTS = 100_000
private const val WORK = 80