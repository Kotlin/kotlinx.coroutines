/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.akka

import akka.actor.*
import com.typesafe.config.*
import org.openjdk.jmh.annotations.*
import scala.concurrent.*
import scala.concurrent.duration.*
import java.util.concurrent.*

const val N_MESSAGES = 100_000

data class Ball(val count: Int)
class Start
class Stop

/*
 * Benchmark                                              (dispatcher)  Mode  Cnt    Score    Error  Units
 * PingPongAkkaBenchmark.coresCountPingPongs        default-dispatcher  avgt   10  277.501 ± 38.583  ms/op
 * PingPongAkkaBenchmark.coresCountPingPongs  single-thread-dispatcher  avgt   10  196.192 ±  9.889  ms/op
 *
 * PingPongAkkaBenchmark.singlePingPong             default-dispatcher  avgt   10  173.742 ± 41.984  ms/op
 * PingPongAkkaBenchmark.singlePingPong       single-thread-dispatcher  avgt   10   24.181 ±  0.730  ms/op
 */
//@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
//@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
//@Fork(value = 2)
//@BenchmarkMode(Mode.AverageTime)
//@OutputTimeUnit(TimeUnit.MILLISECONDS)
//@State(Scope.Benchmark)
open class PingPongAkkaBenchmark {

    lateinit var system: ActorSystem

    @Param("default-dispatcher", "single-thread-dispatcher")
    var dispatcher: String = "akka.actor.default-dispatcher"

    @Setup
    fun setup() {
        system = ActorSystem.create("PingPong", ConfigFactory.parseString("""
            akka.actor.single-thread-dispatcher {
                type = Dispatcher
                executor = "thread-pool-executor"
                thread-pool-executor {
                    fixed-pool-size = 1
                }
                throughput = 1
            }
            """.trimIndent()
        ))
    }

    @TearDown
    fun tearDown() {
        Await.ready(system.terminate(), Duration.Inf())
    }

//    @Benchmark
    fun singlePingPong() {
        runPingPongs(1)
    }

//    @Benchmark
    fun coresCountPingPongs() {
        runPingPongs(Runtime.getRuntime().availableProcessors())
    }

    private fun runPingPongs(pairsCount: Int) {
        val latch = CountDownLatch(pairsCount)
        repeat(pairsCount) {
            val pongRef = system.actorOf(Props.create(PongActorAkka::class.java)
                    .withDispatcher("akka.actor.$dispatcher"))
            val pingRef = system.actorOf(Props.create(PingActorAkka::class.java, pongRef, latch)
                    .withDispatcher("akka.actor.$dispatcher"))
            pingRef.tell(Start(), ActorRef.noSender())
        }

        latch.await()
    }

    class PingActorAkka(val pongRef: ActorRef, val stopLatch: CountDownLatch) : UntypedAbstractActor() {
        override fun onReceive(msg: Any?) {
            when (msg) {
                is Start -> {
                    pongRef.tell(Ball(0), self)
                }
                is Ball -> {
                    pongRef.tell(Ball(count = msg.count + 1), self)
                }
                is Stop -> {
                    stopLatch.countDown()
                    context.stop(self)
                }
                else -> unhandled(msg)
            }
        }
    }

    class PongActorAkka : UntypedAbstractActor() {
        override fun onReceive(msg: Any?) {
            when (msg) {
                is Ball -> {
                    if (msg.count >= N_MESSAGES) {
                        sender.tell(Stop(), self)
                        context.stop(self)
                    } else {
                        sender.tell(Ball(msg.count + 1), self)
                    }
                }
                else -> unhandled(msg)
            }
        }
    }
}
