/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks

import kotlinx.coroutines.*
import org.openjdk.jmh.annotations.*
import org.openjdk.jmh.annotations.State
import java.lang.Thread.*
import java.util.concurrent.*
import kotlin.concurrent.*

/**
 * Inspired by
 * https://github.com/Heapy/kotlin-benchmarks/commit/6b446867886ec54341a180209840bf39c37e1d14
 *
 * Current results:
 * ```
 * Benchmark                                                       Mode  Cnt    Score     Error  Units
 * DispatchersContextSwitchBenchmark.coroutinesBlockingDispatcher  avgt   10   37.172 ±   0.587  ms/op
 * DispatchersContextSwitchBenchmark.coroutinesDefaultDispatcher   avgt   10  149.659 ±   7.954  ms/op
 * DispatchersContextSwitchBenchmark.coroutinesIoDispatcher        avgt   10  522.634 ± 211.396  ms/op
 * DispatchersContextSwitchBenchmark.threads                       avgt   10  714.920 ±  19.840  ms/op
 * ```
 */
@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 10, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Thread)
open class DispatchersContextSwitchBenchmark {
    private val nCoroutines = 10000
    private val delayTimeMs = 1L
    private val nRepeatDelay = 10

    @Benchmark
    open fun coroutinesIoDispatcher() = runBlocking {
        repeat(nCoroutines) {
            launch(Dispatchers.IO) {
                repeat(nRepeatDelay) {
                    delay(delayTimeMs)
                }
            }
        }
    }

    @Benchmark
    open fun coroutinesDefaultDispatcher() = runBlocking {
        repeat(nCoroutines) {
            launch(Dispatchers.Default) {
                repeat(nRepeatDelay) {
                    delay(delayTimeMs)
                }
            }
        }
    }

    @Benchmark
    open fun coroutinesBlockingDispatcher() = runBlocking {
        repeat(nCoroutines) {
            launch {
                repeat(nRepeatDelay) {
                    delay(delayTimeMs)
                }
            }
        }
    }

    @Benchmark
    open fun threads() {
        val threads = List(nCoroutines) {
            thread(start = true) {
                repeat(nRepeatDelay) {
                    sleep(delayTimeMs)
                }
            }
        }
        threads.forEach { it.join() }
    }
}