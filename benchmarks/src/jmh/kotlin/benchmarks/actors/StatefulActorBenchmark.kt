/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.actors

import benchmarks.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*

/*
 * kotlinx-based counterpart of [StatefulActorAkkaBenchmark]
 *
 * Benchmark                                                      (dispatcher)  Mode  Cnt    Score    Error  Units
 * StatefulActorBenchmark.multipleComputationsMultipleRequestors           fjp  avgt   10   81.649 ±  9.671  ms/op
 * StatefulActorBenchmark.multipleComputationsMultipleRequestors         ftp_1  avgt   10  160.590 ± 50.342  ms/op
 * StatefulActorBenchmark.multipleComputationsMultipleRequestors         ftp_8  avgt   10  275.798 ± 32.795  ms/op
 *
 * StatefulActorBenchmark.multipleComputationsSingleRequestor              fjp  avgt   10   67.206 ±  4.023  ms/op
 * StatefulActorBenchmark.multipleComputationsSingleRequestor            ftp_1  avgt   10   17.883 ±  1.314  ms/op
 * StatefulActorBenchmark.multipleComputationsSingleRequestor            ftp_8  avgt   10   77.052 ± 10.132  ms/op
 *
 * StatefulActorBenchmark.singleComputationMultipleRequestors              fjp  avgt   10  488.003 ± 53.014  ms/op
 * StatefulActorBenchmark.singleComputationMultipleRequestors            ftp_1  avgt   10  120.445 ± 24.659  ms/op
 * StatefulActorBenchmark.singleComputationMultipleRequestors            ftp_8  avgt   10  527.118 ± 51.139  ms/op
 *
 * StatefulActorBenchmark.singleComputationSingleRequestor                 fjp  avgt   10   95.030 ± 23.850  ms/op
 * StatefulActorBenchmark.singleComputationSingleRequestor               ftp_1  avgt   10   16.005 ±  0.629  ms/op
 * StatefulActorBenchmark.singleComputationSingleRequestor               ftp_8  avgt   10   76.435 ±  5.076  ms/op
 */
@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 2)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
open class StatefulActorBenchmark : ParametrizedDispatcherBase() {

    data class Letter(val message: Any, val sender: Channel<Letter>)

    @Param("fjp", "ftp_1", "ftp_8", "experimental")
    override var dispatcher: String = "fjp"

    @Benchmark
    fun singleComputationSingleRequestor() = runBlocking {
        run(1, 1)
    }

    @Benchmark
    fun singleComputationMultipleRequestors() = runBlocking {
        run(1, CORES_COUNT)
    }

    @Benchmark
    fun multipleComputationsSingleRequestor() = runBlocking {
        run(CORES_COUNT, 1)
    }

    @Benchmark
    fun multipleComputationsMultipleRequestors() = runBlocking {
        run(CORES_COUNT, CORES_COUNT)
    }

    private suspend fun run(computationActorsCount: Int, requestorActorsCount: Int) {
        val resultChannel: Channel<Unit> = Channel(requestorActorsCount)
        val computations = (0 until computationActorsCount).map { computationActor() }
        val requestors = (0 until requestorActorsCount).map { requestorActor(computations, resultChannel) }

        for (requestor in requestors) {
            requestor.send(Letter(1L, Channel()))
        }

        repeat(requestorActorsCount) {
            resultChannel.receive()
        }
    }

    private fun CoroutineScope.requestorActor(computations: List<SendChannel<Letter>>, stopChannel: Channel<Unit>) =
        actor<Letter>(capacity = 1024) {
            var received = 0
            for (letter in channel) with(letter) {
                when (message) {
                    is Long -> {
                        if (++received >= ROUNDS) {
                            stopChannel.send(Unit)
                            return@actor
                        } else {
                            computations[ThreadLocalRandom.current().nextInt(0, computations.size)]
                                    .send(Letter(ThreadLocalRandom.current().nextLong(), channel))
                        }
                    }
                    else -> error("Cannot happen: $letter")
                }
            }
        }
}

fun CoroutineScope.computationActor(stateSize: Int = STATE_SIZE) =
    actor<StatefulActorBenchmark.Letter>(capacity = 1024) {
        val coefficients = LongArray(stateSize) { ThreadLocalRandom.current().nextLong(0, 100) }

        for (letter in channel) with(letter) {
            when (message) {
                is Long -> {
                    var result = 0L
                    for (coefficient in coefficients) {
                        result += message * coefficient
                    }

                    sender.send(StatefulActorBenchmark.Letter(result, channel))
                }
                is Stop -> return@actor
                else -> error("Cannot happen: $letter")
            }
        }
    }
