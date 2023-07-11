/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.tailcall

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.selects.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*

@Warmup(iterations = 8, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 8, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
open class SelectBenchmark {
    // 450
    private val iterations = 1000

    @Benchmark
    fun stressSelect() = runBlocking {
        val pingPong = Channel<Unit>()
        launch {
            repeat(iterations) {
                select {
                    pingPong.onSend(Unit) {}
                }
            }
        }

        launch {
            repeat(iterations) {
                select {
                    pingPong.onReceive() {}
                }
            }
        }
    }
}
