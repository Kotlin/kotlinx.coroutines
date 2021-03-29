/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.tailcall

import kotlinx.coroutines.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*

@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
open class SimpleChannelBenchmark {

    private val iterations = 10_000

    @Volatile
    private var sink: Int = 0

    @Benchmark
    fun cancellable() = runBlocking {
        val ch = CancellableChannel()
        launch {
            repeat(iterations) { ch.send(it) }
        }

        launch {
            repeat(iterations) { sink = ch.receive() }
        }
    }

    @Benchmark
    fun cancellableReusable() = runBlocking {
        val ch = CancellableReusableChannel()
        launch {
            repeat(iterations) { ch.send(it) }
        }

        launch {
            repeat(iterations) { sink = ch.receive() }
        }
    }

    @Benchmark
    fun nonCancellable() = runBlocking {
        val ch = NonCancellableChannel()
        launch {
            repeat(iterations) { ch.send(it) }
        }

        launch {
            repeat(iterations) {
                sink = ch.receive()
            }
        }
    }
}
