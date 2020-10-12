/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*

@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
open class CombineBenchmark {

    @Benchmark
    fun measure10() = measure(10)

    @Benchmark
    fun measure100() = measure(100)

    @Benchmark
    fun measure1000() = measure(1000)

    fun measure(size: Int) = runBlocking {
        val flowList = (1..size).map { flowOf(it) }
        val listFlow = combine(flowList) { it.toList() }

        listFlow.collect {
        }
    }
}
