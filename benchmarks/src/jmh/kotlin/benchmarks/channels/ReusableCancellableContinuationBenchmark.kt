/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.timeunit.*
import org.openjdk.jmh.annotations.*

/*
 * Benchmark                                                   Mode  Cnt     Score    Error  Units
 * ReusableCancellableContinuationBenchmark.runCancellable     avgt    5  2464.846 ± 24.565  us/op
 * ReusableCancellableContinuationBenchmark.runNonCancellable  avgt    5  1112.962 ±  9.709  us/op
 * ReusableCancellableContinuationBenchmark.runReusable        avgt    5  1615.746 ± 30.324  us/op
 */
@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
open class ReusableCancellableContinuationBenchmark {

    private val iterations = 10_000

    @Volatile
    private var sink: Int = 0

    @Benchmark
    fun runCancellable() = runBlocking {
        val ch = CancellableChannel()
        async {
            repeat(iterations) { ch.send(it) }
        }

        async {
            repeat(iterations) {
                sink = ch.receive()
            }
        }
    }

    @Benchmark
    fun runNonCancellable() = runBlocking {
        val ch = NonCancellableChannel()
        async {
            repeat(iterations) { ch.send(it) }
        }

        async {
            repeat(iterations) {
                sink = ch.receive()
            }
        }
    }

    @Benchmark
    fun runReusable() = runBlocking {
        val ch = ReusableCancellabilityChannel()
        async {
            repeat(iterations) { ch.send(it) }
        }

        async {
            repeat(iterations) {
                sink = ch.receive()
            }
        }

    }
}

