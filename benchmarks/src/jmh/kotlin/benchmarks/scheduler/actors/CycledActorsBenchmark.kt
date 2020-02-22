/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.scheduler.actors

import benchmarks.*
import benchmarks.akka.*
import benchmarks.scheduler.actors.PingPongActorBenchmark.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*

/*
 * Cores count actors chained into single cycle pass message and process it using its private state.
 *
 * Benchmark                           (actorStateSize)  (dispatcher)  Mode  Cnt     Score     Error  Units
 * CycledActorsBenchmark.cycledActors                 1           fjp  avgt   14    22.751 ±   1.351  ms/op
 * CycledActorsBenchmark.cycledActors                 1         ftp_1  avgt   14     4.535 ±   0.076  ms/op
 * CycledActorsBenchmark.cycledActors                 1  experimental  avgt   14     6.728 ±   0.048  ms/op
 *
 * CycledActorsBenchmark.cycledActors              1024           fjp  avgt   14    43.725 ±  14.393  ms/op
 * CycledActorsBenchmark.cycledActors              1024         ftp_1  avgt   14    13.827 ±   1.554  ms/op
 * CycledActorsBenchmark.cycledActors              1024  experimental  avgt   14    23.823 ±   1.643  ms/op
 *
 * CycledActorsBenchmark.cycledActors            262144           fjp  avgt   14  1885.708 ± 532.634  ms/op
 * CycledActorsBenchmark.cycledActors            262144         ftp_1  avgt   14  1394.997 ± 101.938  ms/op
 * CycledActorsBenchmark.cycledActors            262144  experimental  avgt   14  1804.146 ±  57.275  ms/op
 */
@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
open class CycledActorsBenchmark : ParametrizedDispatcherBase() {

    companion object {
        val NO_CHANNEL = Channel<Letter>(0)
    }

    @Param("fjp", "ftp_1", "scheduler")
    override var dispatcher: String = "fjp"

    @Param("1", "1024")
    var actorStateSize = 1

    @Benchmark
    fun cycledActors() = runBlocking {
        val stopChannel = Channel<Unit>(CORES_COUNT)
        runCycle(stopChannel)
        repeat(CORES_COUNT) {
            stopChannel.receive()
        }
    }

    private suspend fun runCycle(stopChannel: Channel<Unit>) {
        val trailingActor = lastActor(stopChannel)

        var previous = trailingActor
        for (i in 1 until CORES_COUNT) {
            previous = createActor(previous, stopChannel)
        }

        trailingActor.send(Letter(Start(), previous))
    }

    private fun lastActor(stopChannel: Channel<Unit>) = actor<Letter>(capacity = 1024) {
        var nextChannel: SendChannel<Letter>? = null
        val state = LongArray(actorStateSize) { ThreadLocalRandom.current().nextLong(1024) }

        for (letter in channel) with(letter) {
            when (message) {
                is Start -> {
                    nextChannel = sender
                    sender.send(Letter(Ball(ThreadLocalRandom.current().nextInt(1, 100)), NO_CHANNEL))
                }
                is Ball -> {
                    nextChannel!!.send(Letter(Ball(transmogrify(message.count, state)), NO_CHANNEL))
                }
                is Stop -> {
                    stopChannel.send(Unit)
                    return@actor
                }
                else -> error("Can't happen")
            }
        }
    }

    private fun createActor(nextActor: SendChannel<Letter>, stopChannel: Channel<Unit>) = actor<Letter>(capacity = 1024) {
        var received = 0
        val state = LongArray(actorStateSize) { ThreadLocalRandom.current().nextLong(1024) }

        for (letter in channel) with(letter) {
            when (message) {
                is Ball -> {
                    if (++received > 1_000) {
                        nextActor.send(Letter(Stop(), NO_CHANNEL))
                        stopChannel.send(Unit)
                        return@actor
                    } else {
                        nextActor.send(Letter(Ball(transmogrify(message.count, state)), NO_CHANNEL))
                    }
                }
                is Stop -> {
                    nextActor.send(Letter(Stop(), NO_CHANNEL))
                    stopChannel.send(Unit)
                }
                else -> error("Can't happen")
            }
        }
    }

    private fun transmogrify(value: Int, coefficients: LongArray): Int {
        var result = 0L
        for (coefficient in coefficients) {
            result += coefficient * value
        }

        return result.toInt()
    }
}
