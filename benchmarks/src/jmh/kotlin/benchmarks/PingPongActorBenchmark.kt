package benchmarks

import akka.actor.*
import kotlinx.coroutines.experimental.CommonPool
import kotlinx.coroutines.experimental.channels.Channel
import kotlinx.coroutines.experimental.channels.SendChannel
import kotlinx.coroutines.experimental.channels.actor
import kotlinx.coroutines.experimental.newFixedThreadPoolContext
import kotlinx.coroutines.experimental.newSingleThreadContext
import kotlinx.coroutines.experimental.runBlocking
import org.openjdk.jmh.annotations.*
import org.openjdk.jmh.annotations.Scope
import java.util.concurrent.TimeUnit
import kotlin.coroutines.experimental.CoroutineContext

/*

Benchmark                                             Mode  Cnt    Score    Error  Units
PingPongActorBenchmark.pingPongAkka                   avgt   15  439.419 ± 24.595  ms/op
PingPongActorBenchmark.pingPongCoroutineCommonPool    avgt   15  809.122 ± 18.102  ms/op
PingPongActorBenchmark.pingPongCoroutineMain          avgt   15  360.072 ±  4.930  ms/op
PingPongActorBenchmark.pingPongCoroutineSingleThread  avgt   15  368.429 ±  3.718  ms/op
PingPongActorBenchmark.pingPongCoroutineTwoThreads    avgt   15  615.514 ±  5.292  ms/op

*/

private const  val N_MESSAGES = 1_000_000

@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 3)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
open class PingPongActorBenchmark {
    data class Ball(val count: Int)
    class Start
    class Stop

    class PingActorAkka(val pongRef: ActorRef) : UntypedActor() {
        override fun onReceive(msg: Any?) {
            when (msg) {
                is Start -> {
                    pongRef.tell(Ball(0), self)
                }
                is Ball -> {
                    pongRef.tell(Ball(count = msg.count + 1), self)
                }
                is Stop -> {
                    context.system().shutdown()
                }
                else -> unhandled(msg)
            }
        }
    }
    
    class PongActorAkka() : UntypedActor() {
        override fun onReceive(msg: Any?) {
            when (msg) {
                is Ball -> {
                    if (msg.count >= N_MESSAGES) {
                        sender.tell(Stop())
                        context.stop(self)
                    } else {
                        sender.tell(Ball(msg.count + 1))
                    }
                }
                else -> unhandled(msg)
            }
        }
    }

    @Benchmark
    fun pingPongAkka() {
        val system = ActorSystem.create("PingPoing")
        val pongRef = system.actorOf(Props(UntypedActorFactory { PongActorAkka() }), "pong")
        val pingRef = system.actorOf(Props(UntypedActorFactory { PingActorAkka(pongRef) }), "ping")
        pingRef.tell(Start())
        system.awaitTermination()
    }

    data class Letter(val msg: Any?, val sender: SendChannel<Letter>)

    fun pingActorCoroutine(context: CoroutineContext, pingChannel: SendChannel<Letter>) = actor<Letter>(context) {
        var initiator: SendChannel<Letter>? = null
        for (letter in channel) with(letter) {
            when (msg) {
                is Start -> {
                    initiator = sender
                    pingChannel.send(Letter(Ball(0), channel))
                }
                is Ball -> {
                    pingChannel.send(Letter(Ball(msg.count + 1), channel))
                }
                is Stop -> {
                    initiator!!.send(Letter(Stop(), channel))
                    return@actor
                }
                else -> error("Cannot happen $msg")
            }
        }
    }

    fun pongActorCoroutine(context: CoroutineContext) = actor<Letter>(context) {
        for (letter in channel) with (letter) {
            when (msg) {
                is Ball -> {
                    if (msg.count >= N_MESSAGES) {
                        sender.send(Letter(Stop(), channel))
                        return@actor
                    } else {
                        sender.send(Letter(Ball(msg.count + 1), channel))
                    }
                }
                else -> error("Cannot happen $msg")
            }
        }
    }

    @Benchmark
    fun pingPongCoroutineCommonPool() = runBlocking<Unit> {
        val pong = pongActorCoroutine(CommonPool)
        val ping = pingActorCoroutine(CommonPool, pong)
        val me = Channel<Letter>()
        ping.send(Letter(Start(), me))
        me.receive()
    }

    @Benchmark
    fun pingPongCoroutineMain() = runBlocking<Unit> {
        val pong = pongActorCoroutine(coroutineContext)
        val ping = pingActorCoroutine(coroutineContext, pong)
        val me = Channel<Letter>()
        ping.send(Letter(Start(), me))
        me.receive()
    }

    val singleThread = newSingleThreadContext("PingPongThread")

    @Benchmark
    fun pingPongCoroutineSingleThread() = runBlocking<Unit> {
        val pong = pongActorCoroutine(singleThread)
        val ping = pingActorCoroutine(singleThread, pong)
        val me = Channel<Letter>()
        ping.send(Letter(Start(), me))
        me.receive()
    }

    val twoThreads = newFixedThreadPoolContext(2, "PingPongThreads")

    @Benchmark
    fun pingPongCoroutineTwoThreads() = runBlocking<Unit> {
        val pong = pongActorCoroutine(twoThreads)
        val ping = pingActorCoroutine(twoThreads, pong)
        val me = Channel<Letter>()
        ping.send(Letter(Start(), me))
        me.receive()
    }
}
