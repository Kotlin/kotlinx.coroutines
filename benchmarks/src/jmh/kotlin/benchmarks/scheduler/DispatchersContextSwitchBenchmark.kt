/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.scheduler

import benchmarks.akka.*
import kotlinx.coroutines.*
import org.openjdk.jmh.annotations.*
import org.openjdk.jmh.annotations.State
import java.lang.Thread.*
import java.util.concurrent.*
import kotlin.concurrent.*
import kotlin.coroutines.*

@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Thread)
open class DispatchersContextSwitchBenchmark {
    private val nCoroutines = 10000
    private val delayTimeMs = 1L
    private val nRepeatDelay = 10

    private val fjp = ForkJoinPool.commonPool().asCoroutineDispatcher()
    private val ftp = Executors.newFixedThreadPool(CORES_COUNT - 1).asCoroutineDispatcher()

    @TearDown
    fun teardown() {
        ftp.close()
        (ftp.executor as ExecutorService).awaitTermination(1, TimeUnit.SECONDS)
    }

    @Benchmark
    fun coroutinesIoDispatcher() =  runBenchmark(Dispatchers.IO)

    @Benchmark
    fun coroutinesDefaultDispatcher() = runBenchmark(Dispatchers.Default)

    @Benchmark
    fun coroutinesFjpDispatcher()  = runBenchmark(fjp)

    @Benchmark
    fun coroutinesFtpDispatcher()  = runBenchmark(ftp)

    @Benchmark
    fun coroutinesBlockingDispatcher() = runBenchmark(EmptyCoroutineContext)

    @Benchmark
    fun threads() {
        val threads = List(nCoroutines) {
            thread(start = true) {
                repeat(nRepeatDelay) {
                    sleep(delayTimeMs)
                }
            }
        }
        threads.forEach { it.join() }
    }

    private fun runBenchmark(dispatcher: CoroutineContext)  = runBlocking {
        repeat(nCoroutines) {
            launch(dispatcher) {
                repeat(nRepeatDelay) {
                    delay(delayTimeMs)
                }
            }
        }
    }
}

