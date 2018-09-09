/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*

/*
 * Benchmark which launches multiple async jobs each with either own private or global shared state,
 * each job iterates over its state multiple times and suspends after every iteration.
 * Benchmark is intended to indicate pros and cons of coroutines affinity (assuming threads are rarely migrated)
 * and comparison with single thread and ForkJoinPool
 *
 * Benchmark                                     (dispatcher)  (jobsCount)  Mode  Cnt    Score    Error  Units
 * StatefulAsyncBenchmark.dependentStateAsync             fjp            1  avgt   10   42.147 ± 11.563  us/op
 * StatefulAsyncBenchmark.dependentStateAsync             fjp            8  avgt   10  111.053 ± 40.097  us/op
 * StatefulAsyncBenchmark.dependentStateAsync             fjp           16  avgt   10  239.992 ± 52.839  us/op
 * StatefulAsyncBenchmark.dependentStateAsync           ftp_1            1  avgt   10   32.851 ± 11.385  us/op
 * StatefulAsyncBenchmark.dependentStateAsync           ftp_1            8  avgt   10   51.692 ±  0.961  us/op
 * StatefulAsyncBenchmark.dependentStateAsync           ftp_1           16  avgt   10  101.511 ±  3.060  us/op
 * StatefulAsyncBenchmark.dependentStateAsync           ftp_8            1  avgt   10   31.549 ±  1.014  us/op
 * StatefulAsyncBenchmark.dependentStateAsync           ftp_8            8  avgt   10  103.990 ±  1.588  us/op
 * StatefulAsyncBenchmark.dependentStateAsync           ftp_8           16  avgt   10  156.384 ±  2.914  us/op
 *
 * StatefulAsyncBenchmark.independentStateAsync           fjp            1  avgt   10   32.503 ±  0.721  us/op
 * StatefulAsyncBenchmark.independentStateAsync           fjp            8  avgt   10   73.000 ±  1.686  us/op
 * StatefulAsyncBenchmark.independentStateAsync           fjp           16  avgt   10   98.629 ±  7.541  us/op
 * StatefulAsyncBenchmark.independentStateAsync         ftp_1            1  avgt   10   26.111 ±  0.814  us/op
 * StatefulAsyncBenchmark.independentStateAsync         ftp_1            8  avgt   10   54.644 ±  1.261  us/op
 * StatefulAsyncBenchmark.independentStateAsync         ftp_1           16  avgt   10  104.871 ±  1.599  us/op
 * StatefulAsyncBenchmark.independentStateAsync         ftp_8            1  avgt   10   31.929 ±  0.698  us/op
 * StatefulAsyncBenchmark.independentStateAsync         ftp_8            8  avgt   10  108.959 ±  1.029  us/op
 * StatefulAsyncBenchmark.independentStateAsync         ftp_8           16  avgt   10  159.593 ±  5.262  us/op
 *
 */
@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 2)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
open class StatefulAsyncBenchmark : ParametrizedDispatcherBase() {

    private val stateSize = 2048
    private val jobSuspensions = 2 // multiplicative factor for throughput

    // it's useful to have more jobs than cores so run queue always will be non empty
    @Param("1", "8", "16")
    var jobsCount = 1

    @Param("fjp", "ftp_1", "ftp_8")
    override var dispatcher: String = "fjp"

    @Volatile
    private var state: Array<LongArray>? = null

    @Setup
    override fun setup() {
        super.setup()
        state = Array(Runtime.getRuntime().availableProcessors() * 4) { LongArray(stateSize) { ThreadLocalRandom.current().nextLong() } }
    }

    @Benchmark
    fun independentStateAsync() = runBlocking {
        val broadcastChannel = BroadcastChannel<Int>(1)
        val subscriptionChannel = Channel<Int>(jobsCount)
        val jobs= (0 until jobsCount).map { launchJob(it, broadcastChannel, subscriptionChannel) }.toList()

        repeat(jobsCount) {
            subscriptionChannel.receive() // await all jobs to start
        }

        // Fire barrier to start execution
        broadcastChannel.send(1)
        jobs.forEach { it.await() }
    }

    @Benchmark
    fun dependentStateAsync() = runBlocking {
        val broadcastChannel = BroadcastChannel<Int>(1)
        val subscriptionChannel = Channel<Int>(jobsCount)
        val jobs= (0 until jobsCount).map { launchJob(0, broadcastChannel, subscriptionChannel) }.toList()

        repeat(jobsCount) {
            subscriptionChannel.receive() // await all jobs to start
        }

        // Fire barrier to start execution
        broadcastChannel.send(1)
        jobs.forEach { it.await() }
    }

    private fun launchJob(
        stateNum: Int,
        channel: BroadcastChannel<Int>,
        subscriptionChannel: Channel<Int>
    ): Deferred<Long> =
        async {
            val subscription = channel.openSubscription()
            subscriptionChannel.send(1)
            subscription.receive()

            var sum = 0L
            repeat(jobSuspensions) {
                val arr = state!![stateNum]
                for (i in 0 until stateSize) {
                    sum += arr[i]

                }

                yield()
            }
            sum
        }
}