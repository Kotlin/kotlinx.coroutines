/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.flow.internal.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*

@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.Throughput)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
open class CombineTwoFlowsBenchmark {

    @Param("100", "100000", "1000000")
    private var size = 100000

    @Benchmark
    fun combinePlain() = runBlocking {
        val flow = (1 until size.toLong()).asFlow()
        flow.combine(flow) { a, b -> a + b }.collect()
    }

    @Benchmark
    fun combineTransform() = runBlocking {
        val flow = (1 until size.toLong()).asFlow()
        flow.combineTransform(flow) { a, b -> emit(a + b) }.collect()
    }

    @Benchmark
    fun combineVararg() = runBlocking {
        val flow = (1 until size.toLong()).asFlow()
        combine(listOf(flow, flow)) { arr -> arr[0] + arr[1] }.collect()
    }

    @Benchmark
    fun combineTransformVararg() = runBlocking {
        val flow = (1 until size.toLong()).asFlow()
        combineTransform(listOf(flow, flow)) { arr -> emit(arr[0] + arr[1]) }.collect()
    }
}
