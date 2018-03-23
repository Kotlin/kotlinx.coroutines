package benchmarks.actors

import benchmarks.ParametrizedDispatcherBase
import kotlinx.coroutines.experimental.channels.Channel
import kotlinx.coroutines.experimental.channels.SendChannel
import kotlinx.coroutines.experimental.channels.actor
import kotlinx.coroutines.experimental.runBlocking
import org.openjdk.jmh.annotations.*
import java.util.concurrent.TimeUnit
import kotlin.coroutines.experimental.CoroutineContext

/*
 * Benchmark                                   (dispatcher)  Mode  Cnt    Score    Error  Units
 * PingPongActorBenchmark.coresCountPingPongs           fjp  avgt   10  200.581 ± 22.669  ms/op
 * PingPongActorBenchmark.coresCountPingPongs         ftp_1  avgt   10  494.334 ± 27.450  ms/op
 * PingPongActorBenchmark.coresCountPingPongs         ftp_2  avgt   10  498.754 ± 27.743  ms/op
 * PingPongActorBenchmark.coresCountPingPongs         ftp_8  avgt   10  804.498 ± 69.826  ms/op
 *
 * PingPongActorBenchmark.singlePingPong                fjp  avgt   10  217.005 ± 18.693  ms/op
 * PingPongActorBenchmark.singlePingPong              ftp_1  avgt   10   57.632 ±  1.835  ms/op
 * PingPongActorBenchmark.singlePingPong              ftp_2  avgt   10  112.723 ±  5.280  ms/op
 * PingPongActorBenchmark.singlePingPong              ftp_8  avgt   10  276.958 ± 21.447  ms/op
 */
@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 2)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
open class PingPongActorBenchmark : ParametrizedDispatcherBase() {
    data class Letter(val message: Any?, val sender: SendChannel<Letter>)

    @Param("fjp", "ftp_1", "ftp_2", "ftp_8", "experimental")
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
            val pong = pongActorCoroutine(benchmarkContext)
            val ping = pingActorCoroutine(benchmarkContext, pong)
            ping.send(Letter(Start(), me))
        }

        repeat(count) {
            me.receive()
        }
    }

    private fun pingActorCoroutine(context: CoroutineContext, pingChannel: SendChannel<Letter>,
                                   capacity: Int = 1) = actor<Letter>(context, capacity = capacity) {
        var initiator: SendChannel<Letter>? = null
        for (letter in channel) with(letter) {
            when (message) {
                is Start -> {
                    initiator = sender
                    pingChannel.send(Letter(Ball(0), channel))
                }
                is Ball -> {
                    pingChannel.send(Letter(Ball(message.count + 1), channel))
                }
                is Stop -> {
                    initiator!!.send(Letter(Stop(), channel))
                    return@actor
                }
                else -> error("Cannot happen $message")
            }
        }
    }

    private fun pongActorCoroutine(context: CoroutineContext, capacity: Int = 1) = actor<Letter>(context, capacity = capacity) {
        for (letter in channel) with(letter) {
            when (message) {
                is Ball -> {
                    if (message.count >= N_MESSAGES) {
                        sender.send(Letter(Stop(), channel))
                        return@actor
                    } else {
                        sender.send(Letter(Ball(message.count + 1), channel))
                    }
                }
                else -> error("Cannot happen $message")
            }
        }
    }
}