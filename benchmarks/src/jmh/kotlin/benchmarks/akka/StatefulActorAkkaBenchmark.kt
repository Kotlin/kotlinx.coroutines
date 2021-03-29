/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.akka

import akka.actor.*
import com.typesafe.config.*
import org.openjdk.jmh.annotations.*
import scala.concurrent.*
import scala.concurrent.duration.*
import java.util.concurrent.*

const val ROUNDS = 10_000
const val STATE_SIZE = 1024
val CORES_COUNT = Runtime.getRuntime().availableProcessors()

/*
 * Benchmarks following computation pattern:
 * N actors, each has independent state (coefficients), receives numbers and answers with product and
 * N requestors, which randomly send requests. N roundtrips over every requestor are measured
 *
 * Benchmark                                                                      (dispatcher)  Mode  Cnt    Score    Error  Units
 * StatefulActorAkkaBenchmark.multipleComputationsMultipleRequestors        default-dispatcher  avgt   14   72.568 ± 10.620  ms/op
 * StatefulActorAkkaBenchmark.multipleComputationsMultipleRequestors  single-thread-dispatcher  avgt   14   70.198 ±  3.594  ms/op
 *
 * StatefulActorAkkaBenchmark.multipleComputationsSingleRequestor           default-dispatcher  avgt   14   36.737 ±  3.589  ms/op
 * StatefulActorAkkaBenchmark.multipleComputationsSingleRequestor     single-thread-dispatcher  avgt   14    9.050 ±  0.385  ms/op
 *
 * StatefulActorAkkaBenchmark.singleComputationMultipleRequestors           default-dispatcher  avgt   14  446.563 ± 85.577  ms/op
 * StatefulActorAkkaBenchmark.singleComputationMultipleRequestors     single-thread-dispatcher  avgt   14   70.250 ±  3.104  ms/op
 *
 * StatefulActorAkkaBenchmark.singleComputationSingleRequestor              default-dispatcher  avgt   14   39.964 ±  2.343  ms/op
 * StatefulActorAkkaBenchmark.singleComputationSingleRequestor        single-thread-dispatcher  avgt   14   10.214 ±  2.152  ms/op
 */
//@Warmup(iterations = 7, time = 1, timeUnit = TimeUnit.SECONDS)
//@Measurement(iterations = 7, time = 1, timeUnit = TimeUnit.SECONDS)
//@Fork(value = 2)
//@BenchmarkMode(Mode.AverageTime)
//@OutputTimeUnit(TimeUnit.MILLISECONDS)
//@State(Scope.Benchmark)
open class StatefulActorAkkaBenchmark {

    lateinit var system: ActorSystem

    @Param("default-dispatcher", "single-thread-dispatcher")
    var dispatcher: String = "akka.actor.default-dispatcher"

    @Setup
    fun setup() {
        // TODO extract it to common AkkaBase if new benchmark will appear
        system = ActorSystem.create("StatefulActors", ConfigFactory.parseString("""
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
    fun singleComputationSingleRequestor() {
        run(1, 1)
    }

//    @Benchmark
    fun singleComputationMultipleRequestors() {
        run(1, CORES_COUNT)
    }

//    @Benchmark
    fun multipleComputationsSingleRequestor() {
        run(CORES_COUNT, 1)
    }

//    @Benchmark
    fun multipleComputationsMultipleRequestors() {
        run(CORES_COUNT, CORES_COUNT)
    }

    private fun run(computationActors: Int, requestorActors: Int) {
        val stopLatch = CountDownLatch(requestorActors)
        /*
         * For complex setups Akka creates actors slowly,
         * so first start message may become dead letter (and freeze benchmark)
         */
        val initLatch = CountDownLatch(computationActors + requestorActors)
        val computations = createComputationActors(initLatch, computationActors)
        val requestors = createRequestorActors(requestorActors, computations, initLatch, stopLatch)

        initLatch.await()
        for (requestor in requestors) {
            requestor.tell(1L, ActorRef.noSender())
        }

        stopLatch.await()
        computations.forEach { it.tell(Stop(), ActorRef.noSender()) }
    }

    private fun createRequestorActors(requestorActors: Int, computations: List<ActorRef>, initLatch: CountDownLatch, stopLatch: CountDownLatch): List<ActorRef> {
        return (0 until requestorActors).map {
            system.actorOf(Props.create(RequestorActor::class.java, computations, initLatch, stopLatch)
                    .withDispatcher("akka.actor.$dispatcher"))
        }
    }

    private fun createComputationActors(initLatch: CountDownLatch, count: Int): List<ActorRef> {
        return (0 until count).map {
            system.actorOf(Props.create(
                ComputationActor::class.java,
                    LongArray(STATE_SIZE) { ThreadLocalRandom.current().nextLong(0, 100) }, initLatch)
                    .withDispatcher("akka.actor.$dispatcher"))
        }
    }

    class RequestorActor(val computations: List<ActorRef>, val initLatch: CountDownLatch,
                         val stopLatch: CountDownLatch) : UntypedAbstractActor() {
        private var received = 0

        override fun onReceive(message: Any?) {
            when (message) {
                is Long -> {
                    if (++received >= ROUNDS) {
                        context.stop(self)
                        stopLatch.countDown()
                    } else {
                        computations[ThreadLocalRandom.current().nextInt(0, computations.size)]
                                .tell(ThreadLocalRandom.current().nextLong(), self)
                    }
                }
                else -> unhandled(message)
            }
        }

        override fun preStart() {
            initLatch.countDown()
        }
    }

    class ComputationActor(val coefficients: LongArray, val initLatch: CountDownLatch) : UntypedAbstractActor() {
        override fun onReceive(message: Any?) {
            when (message) {
                is Long -> {
                    var result = 0L
                    for (coefficient in coefficients) {
                        result += coefficient * message
                    }
                    sender.tell(result, self)
                }
                is Stop -> {
                    context.stop(self)
                }
                else -> unhandled(message)
            }
        }

        override fun preStart() {
            initLatch.countDown()
        }
    }
}
