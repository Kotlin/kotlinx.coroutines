/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.actors

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.scheduling.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*
import kotlin.coroutines.*


/*
 * Benchmark                                                  Mode  Cnt    Score     Error  Units
 * PingPongWithBlockingContext.commonPoolWithContextPingPong  avgt   20  972.662 ± 103.448  ms/op
 * PingPongWithBlockingContext.limitingDispatcherPingPong     avgt   20  136.167 ±   4.971  ms/op
 * PingPongWithBlockingContext.withContextPingPong            avgt   20  761.669 ±  41.371  ms/op
 */
@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 10, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 2)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
open class PingPongWithBlockingContext {

    private val experimental = ExperimentalCoroutineDispatcher(8)
    private val blocking = experimental.blocking(8)
    private val threadPool = newFixedThreadPoolContext(8, "PongCtx")

    @TearDown
    fun tearDown() {
        threadPool.close()
    }


    @Benchmark
    fun limitingDispatcherPingPong() = runBlocking {
        runPingPongs(experimental, blocking)
    }


    @Benchmark
    fun withContextPingPong() = runBlocking {
        runPingPongs(experimental, threadPool)
    }

    @Benchmark
    fun commonPoolWithContextPingPong() = runBlocking {
        runPingPongs(ForkJoinPool.commonPool().asCoroutineDispatcher(), threadPool)
    }

    private suspend fun runPingPongs(pingContext: CoroutineContext, pongContext: CoroutineContext) {
        val me = Channel<PingPongActorBenchmark.Letter>()
        val pong = pongActorCoroutine(pongContext)
        val ping = pingActorCoroutine(pingContext, pong)
        ping.send(PingPongActorBenchmark.Letter(Start(), me))

        me.receive()
    }
}
