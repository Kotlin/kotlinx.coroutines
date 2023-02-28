/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks

import kotlinx.coroutines.*
import kotlinx.coroutines.sync.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.TimeUnit
import kotlin.test.*

@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 10, time = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
@Fork(1)
open class SequentialSemaphoreAsMutexBenchmark {
    val s = Semaphore(1)

    @Benchmark
    fun benchmark() : Unit = runBlocking {
        val s = Semaphore(permits = 1, acquiredPermits = 1)
        var step = 0
        launch(Dispatchers.Unconfined) {
            repeat(N) {
                assertEquals(it * 2, step)
                step++
                s.acquire()
            }
        }
        repeat(N) {
            assertEquals(it * 2 + 1, step)
            step++
            s.release()
        }
    }
}

fun main() = SequentialSemaphoreAsMutexBenchmark().benchmark()

private val N = 1_000_000