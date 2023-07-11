/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks

import benchmarks.common.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.scheduling.*
import kotlinx.coroutines.selects.select
import org.openjdk.jmh.annotations.*
import java.lang.Integer.max
import java.util.concurrent.Phaser
import java.util.concurrent.TimeUnit


/**
 * Benchmark to measure channel algorithm performance in terms of average time per `send-receive` pair;
 * actually, it measures the time for a batch of such operations separated into the specified number of consumers/producers.
 * It uses different channels (rendezvous, buffered, unlimited; see [ChannelCreator]) and different dispatchers
 * (see [DispatcherCreator]). If the [_3_withSelect] property is set, it invokes `send` and
 * `receive` via [select], waiting on a local dummy channel simultaneously, simulating a "cancellation" channel.
 *
 * Please, be patient, this benchmark takes quite a lot of time to complete.
 */
@Warmup(iterations = 3, time = 500, timeUnit = TimeUnit.MICROSECONDS)
@Measurement(iterations = 20, time = 500, timeUnit = TimeUnit.MICROSECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.Throughput)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
open class ChannelProducerConsumerBenchmark {
    @Param
    private var _0_dispatcher: DispatcherCreator = DispatcherCreator.DEFAULT

    @Param
    private var _1_channel: ChannelCreator = ChannelCreator.RENDEZVOUS

    @Param("0", "1000")
    private var _2_coroutines: Int = 0

    @Param("false", "true")
    private var _3_withSelect: Boolean = false

    @Param("1", "2", "4", "8", "16") // local machine
//    @Param("1", "2", "4", "8", "16", "32", "64", "128") // Server
    private var _4_parallelism: Int = 0

    @Param("50")
    private var _5_workSize: Int = 0

    private lateinit var dispatcher: CoroutineDispatcher
    private lateinit var channel: Channel<Int>

    @InternalCoroutinesApi
    @Setup
    fun setup() {
        dispatcher = _0_dispatcher.create(_4_parallelism)
        channel = _1_channel.create()
    }

    @Benchmark
    fun mcsp() {
        if (_2_coroutines != 0) return
        val producers = max(1, _4_parallelism - 1)
        val consumers = 1
        run(producers, consumers)
    }

    @Benchmark
    fun spmc() {
        if (_2_coroutines != 0) return
        val producers = 1
        val consumers = max(1, _4_parallelism - 1)
        run(producers, consumers)
    }

    @Benchmark
    fun mpmc() {
        val producers = if (_2_coroutines == 0) (_4_parallelism + 1) / 2 else _2_coroutines / 2
        val consumers = producers
        run(producers, consumers)
    }

    private fun run(producers: Int, consumers: Int) {
        val n = (APPROX_BATCH_SIZE / producers * producers) / consumers * consumers
        val phaser = Phaser(producers + consumers + 1)
        // Run producers
        repeat(producers) {
            GlobalScope.launch(dispatcher) {
                val dummy = if (_3_withSelect) _1_channel.create() else null
                repeat(n / producers) {
                    produce(it, dummy)
                }
                phaser.arrive()
            }
        }
        // Run consumers
        repeat(consumers) {
            GlobalScope.launch(dispatcher) {
                val dummy = if (_3_withSelect) _1_channel.create() else null
                repeat(n / consumers) {
                    consume(dummy)
                }
                phaser.arrive()
            }
        }
        // Wait until work is done
        phaser.arriveAndAwaitAdvance()
    }

    private suspend fun produce(element: Int, dummy: Channel<Int>?) {
        if (_3_withSelect) {
            select<Unit> {
                channel.onSend(element) {}
                dummy!!.onReceive {}
            }
        } else {
            channel.send(element)
        }
        doWork(_5_workSize)
    }

    private suspend fun consume(dummy: Channel<Int>?) {
        if (_3_withSelect) {
            select<Unit> {
                channel.onReceive {}
                dummy!!.onReceive {}
            }
        } else {
            channel.receive()
        }
        doWork(_5_workSize)
    }
}

enum class DispatcherCreator(val create: (parallelism: Int) -> CoroutineDispatcher) {
    //FORK_JOIN({ parallelism ->  ForkJoinPool(parallelism).asCoroutineDispatcher() }),
    @Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
    DEFAULT({ parallelism -> ExperimentalCoroutineDispatcher(corePoolSize = parallelism, maxPoolSize = parallelism) })
}

enum class ChannelCreator(private val capacity: Int) {
    RENDEZVOUS(Channel.RENDEZVOUS),
    BUFFERED_16(16),
    BUFFERED_64(64),
    BUFFERED_UNLIMITED(Channel.UNLIMITED);

    fun create(): Channel<Int> = Channel(capacity)
}

private fun doWork(workSize: Int): Unit = doGeomDistrWork(workSize)

private const val APPROX_BATCH_SIZE = 100_000
