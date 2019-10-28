/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*

@Warmup(iterations = 7, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 7, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
open class FlatMapMergeBenchmark {

    // Note: tests only absence of contention on downstream

    @Param("10", "100", "1000")
    private var iterations = 100

    @Benchmark
    fun flatMapUnsafe() = runBlocking {
        benchmarks.flow.scrabble.flow {
            repeat(iterations) { emit(it) }
        }.flatMapMerge { value ->
            flowOf(value)
        }.collect {
            if (it == -1) error("")
        }
    }

    @Benchmark
    fun flatMapSafe() = runBlocking {
        kotlinx.coroutines.flow.flow {
            repeat(iterations) { emit(it) }
        }.flatMapMerge { value ->
            flowOf(value)
        }.collect {
            if (it == -1) error("")
        }
    }

}