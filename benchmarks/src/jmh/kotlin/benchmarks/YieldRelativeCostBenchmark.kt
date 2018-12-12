/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks

import org.openjdk.jmh.annotations.*
import org.openjdk.jmh.infra.*
import java.util.concurrent.*

@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 2)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@State(Scope.Benchmark)
open class YieldRelativeCostBenchmark {

    @Param("1", "10", "100", "1000")
    var iterations: Int = 10

    @Benchmark
    fun yields() {
        repeat(iterations) {
            Thread.yield()
        }
    }

    @Benchmark
    fun spins(bh: Blackhole) {
        repeat(iterations) {
            bh.consume(it)
        }
    }
}
