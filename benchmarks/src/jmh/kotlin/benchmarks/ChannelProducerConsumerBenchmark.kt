/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks

import benchmarks.common.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.selects.select
import org.openjdk.jmh.annotations.*
import java.lang.Integer.max
import java.util.concurrent.*


/**
 * Benchmark to measure channel algorithm performance in terms of average time per `send-receive` pair;
 * actually, it measures the time for a batch of such operations separated into the specified number of consumers/producers.
 * It uses different channels (rendezvous, buffered, unlimited; see [ChannelCreator]) and different dispatchers
 * (see [DispatcherCreator]). If the [_3_withSelect] property is set, it invokes `send` and
 * `receive` via [select], waiting on a local dummy channel simultaneously, simulating a "cancellation" channel.
 *
 * Please, be patient, this benchmark takes quite a lot of time to complete.
 */
@Warmup(iterations = 5, time = 500, timeUnit = TimeUnit.MILLISECONDS)
@Measurement(iterations = 20, time = 500, timeUnit = TimeUnit.MILLISECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.Throughput)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
open class ChannelProducerConsumerBenchmark {
    private val elements = Array(APPROX_BATCH_SIZE) { "$it" }

    @Param
    private var _0_dispatcher: DispatcherCreator = DispatcherCreator.values()[0]

    @Param
    private var _4_channel: ChannelCreator = ChannelCreator.values()[0]

    @Param("0", "1000")
    private var _2_coroutines: Int = 0

//    @Param("false", "true")
    private var _3_withSelect: Boolean = false

//    @Param("1") // local machine
//    @Param("32", "128")
//    @Param("1", "2", "4", "8", "16", "32", "64", "96") // Google Cloud
    @Param("1", "2", "4", "8", "16", "32", "64", "128")
    private var _1_parallelism: Int = 0

    private lateinit var dispatcher: CoroutineDispatcher
    private lateinit var channel: Channel<String>

    @InternalCoroutinesApi
    @Setup
    fun setup() {
        dispatcher = _0_dispatcher.create(_1_parallelism)
        channel = _4_channel.create()
    }

    @TearDown
    fun after() {
        ((dispatcher as? ExecutorCoroutineDispatcher)?.executor as? ExecutorService)?.shutdown()
    }

    @Benchmark
    fun spmc() {
        if (_2_coroutines != 0) return
        val producers = 1
        val consumers = max(1, _1_parallelism - 1)
        run(producers, consumers)
    }

    @Benchmark
    fun mpsc() {
        if (_2_coroutines != 0) return
        val producers = max(1, _1_parallelism - 1)
        val consumers = 1
        run(producers, consumers)
    }

    @Benchmark
    fun mpmc() {
        val producers = if (_2_coroutines == 0) (_1_parallelism + 1) / 2 else _2_coroutines / 2
        val consumers = producers
        run(producers, consumers)
    }

    private fun run(producers: Int, consumers: Int) {
        val n = APPROX_BATCH_SIZE / producers * producers / consumers * consumers
        val phaser = Phaser(producers + consumers + 1)
        // Run producers
        repeat(producers) {
            GlobalScope.launch(dispatcher) {
                val dummy = if (_3_withSelect) _4_channel.create() else null
                repeat(n / producers) {
                    produce(it, dummy)
                }
                phaser.arrive()
            }
        }
        // Run consumers
        repeat(consumers) {
            GlobalScope.launch(dispatcher) {
                val dummy = if (_3_withSelect) _4_channel.create() else null
                repeat(n / consumers) {
                    consume(dummy)
                }
                phaser.arrive()
            }
        }
        // Wait until work is done
        phaser.arriveAndAwaitAdvance()
    }

    private suspend fun produce(elementIndex: Int, dummy: Channel<String>?) {
        doWork()
        if (_3_withSelect) {
            select<Unit> {
                channel.onSend(elements[elementIndex]) {}
                dummy!!.onReceive {}
            }
        } else {
            channel.send(elements[elementIndex])
        }
    }

    private suspend fun consume(dummy: Channel<String>?) {
        doWork()
        if (_3_withSelect) {
            select<Unit> {
                channel.onReceive {}
                dummy!!.onReceive {}
            }
        } else {
            channel.receive()
        }
    }
}

@Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")
enum class DispatcherCreator(val create: (parallelism: Int) -> CoroutineDispatcher) {
//    DEFAULT({ parallelism -> kotlinx.coroutines.scheduling.ExperimentalCoroutineDispatcher(parallelism, parallelism, "DEFAULT")}),
    FORK_JOIN({ parallelism -> ForkJoinPool(parallelism).asCoroutineDispatcher()}),
//    FIXED_THREAD_POOL({ parallelism ->  Executors.newFixedThreadPool(parallelism).asCoroutineDispatcher() })
}

enum class ChannelCreator(val create: () -> Channel<String>) {
    OLD_RENDEZVOUS({ OldChannel(Channel.RENDEZVOUS) }),
//    OLD_BUFFERED_16({ OldChannel(16) }),
    OLD_BUFFERED_64({ OldChannel(64) }),
//    OLD_UNLIMITED({ OldChannel(Channel.UNLIMITED) }),
    EUROPAR( {kotlinx.coroutines.channels.RendezvousChannelEuropar()} ),
    MSQUEUE({kotlinx.coroutines.channels.RendezvousChannelMSQueue()}),
    RENDEZVOUS({ Channel(Channel.RENDEZVOUS) }),
    //    BUFFERED_16({ Channel(16) }),
    BUFFERED_64({ Channel(64) }),
//    UNLIMITED({ Channel(Channel.UNLIMITED) }),
    ;
}

private fun doWork(): Unit = doGeomDistrWork(100)

private const val APPROX_BATCH_SIZE = 100000
