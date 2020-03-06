/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.scheduler.actors

import benchmarks.*
import benchmarks.akka.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*

/*
 * Benchmark                                   (dispatcher)  Mode  Cnt    Score    Error  Units
 * PingPongActorBenchmark.coresCountPingPongs  experimental  avgt   10  185.066 ± 21.692  ms/op
 * PingPongActorBenchmark.coresCountPingPongs           fjp  avgt   10  200.581 ± 22.669  ms/op
 * PingPongActorBenchmark.coresCountPingPongs         ftp_1  avgt   10  494.334 ± 27.450  ms/op
 * PingPongActorBenchmark.coresCountPingPongs         ftp_2  avgt   10  498.754 ± 27.743  ms/op
 * PingPongActorBenchmark.coresCountPingPongs         ftp_8  avgt   10  804.498 ± 69.826  ms/op
 *
 * PingPongActorBenchmark.singlePingPong       experimental  avgt   10   45.521 ±  3.281  ms/op
 * PingPongActorBenchmark.singlePingPong                fjp  avgt   10  217.005 ± 18.693  ms/op
 * PingPongActorBenchmark.singlePingPong              ftp_1  avgt   10   57.632 ±  1.835  ms/op
 * PingPongActorBenchmark.singlePingPong              ftp_2  avgt   10  112.723 ±  5.280  ms/op
 * PingPongActorBenchmark.singlePingPong              ftp_8  avgt   10  276.958 ± 21.447  ms/op
 */
@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
open class PingPongActorBenchmark : ParametrizedDispatcherBase() {
    data class Letter(val message: Any?, val sender: SendChannel<Letter>)

    @Param("scheduler", "fjp", "ftp_1")
    override var dispatcher: String = "fjp"

    @Benchmark
    fun singlePingPong() = runBlocking {
        runPingPongs(1)
    }

    @Benchmark
    fun coresCountPingPongs() = runBlocking {
        runPingPongs(Runtime.getRuntime().availableProcessors())
    }

    private suspend fun runPingPongs(count: Int) {
        val me = Channel<Letter>()
        repeat(count) {
            val pong = pongActorCoroutine()
            val ping = pingActorCoroutine(pong)
            ping.send(Letter(Start(), me))
        }

        repeat(count) {
            me.receive()
        }
    }
}

fun CoroutineScope.pingActorCoroutine(
    pingChannel: SendChannel<PingPongActorBenchmark.Letter>,
    capacity: Int = 1
) =
    actor<PingPongActorBenchmark.Letter>(capacity = capacity) {
        var initiator: SendChannel<PingPongActorBenchmark.Letter>? = null
        for (letter in channel) with(letter) {
            when (message) {
                is Start -> {
                    initiator = sender
                    pingChannel.send(PingPongActorBenchmark.Letter(Ball(0), channel))
                }
                is Ball -> {
                    pingChannel.send(PingPongActorBenchmark.Letter(Ball(message.count + 1), channel))
                }
                is Stop -> {
                    initiator!!.send(PingPongActorBenchmark.Letter(Stop(), channel))
                    return@actor
                }
                else -> error("Cannot happen $message")
            }
        }
    }

fun CoroutineScope.pongActorCoroutine(capacity: Int = 1) =
    actor<PingPongActorBenchmark.Letter>(capacity = capacity) {
        for (letter in channel) with(letter) {
            when (message) {
                is Ball -> {
                    if (message.count >= N_MESSAGES) {
                        sender.send(PingPongActorBenchmark.Letter(Stop(), channel))
                        return@actor
                    } else {
                        sender.send(PingPongActorBenchmark.Letter(Ball(message.count + 1), channel))
                    }
                }
                else -> error("Cannot happen $message")
            }
        }
    }
