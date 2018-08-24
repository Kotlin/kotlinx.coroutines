/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.actors

import benchmarks.ParametrizedDispatcherBase
import benchmarks.actors.StatefulActorBenchmark.Letter
import kotlinx.coroutines.experimental.channels.Channel
import kotlinx.coroutines.experimental.channels.SendChannel
import kotlinx.coroutines.experimental.channels.actor
import kotlinx.coroutines.experimental.runBlocking
import org.openjdk.jmh.annotations.*
import java.util.concurrent.ThreadLocalRandom
import java.util.concurrent.TimeUnit
import kotlin.coroutines.experimental.CoroutineContext

/*
 * Noisy benchmarks useful to measure scheduling fairness and migration of affinity-sensitive tasks.
 *
 * Benchmark: single actor fans out requests to all (#cores count) computation actors and then ping pongs each in loop.
 * Fair benchmark expects that every computation actor will receive exactly N messages, unfair expects N * cores messages received in total.
 *
 * Benchmark                                                    (dispatcher)  (stateSize)  Mode  Cnt      Score      Error  Units
 * ConcurrentStatefulActorBenchmark.multipleComputationsFair             fjp         1024  avgt    5    215.439 ±   29.685  ms/op
 * ConcurrentStatefulActorBenchmark.multipleComputationsFair           ftp_1         1024  avgt    5     85.374 ±    4.477  ms/op
 * ConcurrentStatefulActorBenchmark.multipleComputationsFair           ftp_8         1024  avgt    5    418.510 ±   46.906  ms/op
 * ConcurrentStatefulActorBenchmark.multipleComputationsFair    experimental         1024  avgt    5    165.250 ±   20.309  ms/op
 *
 * ConcurrentStatefulActorBenchmark.multipleComputationsFair             fjp         8192  avgt    5    220.576 ±   35.596  ms/op
 * ConcurrentStatefulActorBenchmark.multipleComputationsFair           ftp_1         8192  avgt    5    298.276 ±   22.256  ms/op
 * ConcurrentStatefulActorBenchmark.multipleComputationsFair           ftp_8         8192  avgt    5    426.105 ±   29.870  ms/op
 * ConcurrentStatefulActorBenchmark.multipleComputationsFair    experimental         8192  avgt    5    288.546 ±   20.280  ms/op
 *
 * ConcurrentStatefulActorBenchmark.multipleComputationsFair             fjp       262144  avgt    5   4146.057 ±  284.377  ms/op
 * ConcurrentStatefulActorBenchmark.multipleComputationsFair           ftp_1       262144  avgt    5  10250.107 ± 1421.253  ms/op
 * ConcurrentStatefulActorBenchmark.multipleComputationsFair           ftp_8       262144  avgt    5   6761.283 ± 4091.452  ms/op
 * ConcurrentStatefulActorBenchmark.multipleComputationsFair    experimental       262144  avgt    5   6521.436 ±  346.726  ms/op
 *
 * ConcurrentStatefulActorBenchmark.multipleComputationsUnfair           fjp         1024  avgt    5    289.875 ±   14.241  ms/op
 * ConcurrentStatefulActorBenchmark.multipleComputationsUnfair         ftp_1         1024  avgt    5     87.336 ±    5.160  ms/op
 * ConcurrentStatefulActorBenchmark.multipleComputationsUnfair         ftp_8         1024  avgt    5    430.718 ±   23.497  ms/op
 * ConcurrentStatefulActorBenchmark.multipleComputationsUnfair  experimental         1024  avgt    5    153.704 ±   13.869  ms/op
 *
 * ConcurrentStatefulActorBenchmark.multipleComputationsUnfair           fjp         8192  avgt    5    289.836 ±    9.719  ms/op
 * ConcurrentStatefulActorBenchmark.multipleComputationsUnfair         ftp_1         8192  avgt    5    299.523 ±   17.357  ms/op
 * ConcurrentStatefulActorBenchmark.multipleComputationsUnfair         ftp_8         8192  avgt    5    433.959 ±   27.669  ms/op
 * ConcurrentStatefulActorBenchmark.multipleComputationsUnfair  experimental         8192  avgt    5    283.441 ±   22.740  ms/op
 *
 * ConcurrentStatefulActorBenchmark.multipleComputationsUnfair           fjp       262144  avgt    5   7804.066 ± 1386.595  ms/op
 * ConcurrentStatefulActorBenchmark.multipleComputationsUnfair         ftp_1       262144  avgt    5  11142.530 ±  381.401  ms/op
 * ConcurrentStatefulActorBenchmark.multipleComputationsUnfair         ftp_8       262144  avgt    5   7739.136 ± 1317.885  ms/op
 * ConcurrentStatefulActorBenchmark.multipleComputationsUnfair  experimental       262144  avgt    5   7076.911 ± 1971.615  ms/op
 *
 */
@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
open class ConcurrentStatefulActorBenchmark : ParametrizedDispatcherBase() {

    @Param("1024", "8192", "262144")
    var stateSize: Int = -1

    @Param("fjp", "ftp_1", "ftp_8", "experimental")
    override var dispatcher: String = "fjp"

    @Benchmark
    fun multipleComputationsUnfair() = runBlocking {
        val resultChannel: Channel<Unit> = Channel(1)
        val computations = (0 until CORES_COUNT).map { computationActor(benchmarkContext, stateSize) }
        val requestor = requestorActorUnfair(benchmarkContext, computations, resultChannel)
        requestor.send(Letter(Start(), Channel(0)))
        resultChannel.receive()
    }

    @Benchmark
    fun multipleComputationsFair() = runBlocking {
        val resultChannel: Channel<Unit> = Channel(1)
        val computations = (0 until CORES_COUNT).map { computationActor(benchmarkContext, stateSize) }
        val requestor = requestorActorFair(benchmarkContext, computations, resultChannel)
        requestor.send(Letter(Start(), Channel(0)))
        resultChannel.receive()
    }

    fun requestorActorUnfair(context: CoroutineContext, computations: List<SendChannel<Letter>>,
                             stopChannel: Channel<Unit>) = actor<Letter>(context, 1024) {
        var received = 0
        for (letter in channel) with(letter) {
            when (message) {
                is Start -> {
                    computations.shuffled().forEach { it.send(Letter(ThreadLocalRandom.current().nextLong(), channel)) }
                }
                is Long -> {
                    if (++received >= ROUNDS * 8) {
                        stopChannel.send(Unit)
                        return@actor
                    } else {
                        sender.send(Letter(ThreadLocalRandom.current().nextLong(), channel))
                    }
                }
                else -> error("Cannot happen: $letter")
            }
        }
    }


    fun requestorActorFair(context: CoroutineContext, computations: List<SendChannel<Letter>>,
                           stopChannel: Channel<Unit>) = actor<Letter>(context, 1024) {
        val received = hashMapOf(*computations.map { it to 0 }.toTypedArray())
        var receivedTotal = 0

        for (letter in channel) with(letter) {
            when (message) {
                is Start -> {
                    computations.shuffled().forEach { it.send(Letter(ThreadLocalRandom.current().nextLong(), channel)) }
                }
                is Long -> {
                    if (++receivedTotal >= ROUNDS * computations.size) {
                        stopChannel.send(Unit)
                        return@actor
                    } else {
                        val receivedFromSender = received[sender]!!
                        if (receivedFromSender <= ROUNDS) {
                            received[sender] = receivedFromSender + 1
                            sender.send(Letter(ThreadLocalRandom.current().nextLong(), channel))
                        }
                    }
                }
                else -> error("Cannot happen: $letter")
            }
        }
    }
}