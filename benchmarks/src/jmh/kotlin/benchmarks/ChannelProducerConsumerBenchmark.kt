/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.channels.koval_europar.*
import kotlinx.coroutines.selects.select
import org.openjdk.jmh.annotations.*
import org.openjdk.jmh.infra.Blackhole
import java.lang.Integer.max
import java.util.concurrent.Phaser
import java.util.concurrent.ThreadLocalRandom
import java.util.concurrent.TimeUnit
import kotlinx.coroutines.scheduling.ExperimentalCoroutineDispatcher


/**
 * Benchmark to measure channel algorithm performance in terms of average time per `send-receive` pair;
 * actually, it measures the time for a batch of such operations separated into the specified number of consumers/producers.
 * It uses different channels (rendezvous, buffered, unlimited; see [ChannelCreator]) and different dispatchers
 * (see [DispatcherCreator]). If the [_3_withSelect] property is set, it invokes `send` and
 * `receive` via [select], waiting on a local dummy channel simultaneously, simulating a "cancellation" channel.
 *
 * Please, be patient, this benchmark takes quite a lot of time to complete.
 */
@Warmup(iterations = 3, time = 500, timeUnit = TimeUnit.MILLISECONDS)
@Measurement(iterations = 20, time = 500, timeUnit = TimeUnit.MILLISECONDS)
@Fork(value = 3)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
open class ChannelProducerConsumerBenchmark {
    @Param
    private var _0_dispatcher: DispatcherCreator = DispatcherCreator.DEFAULT

    @Param
    private var _1_channel: ChannelCreator = ChannelCreator.KOTLIN_RENDEZVOUS

    @Param("0", "1000")
    private var _2_coroutines: Int = 0

    @Param("false", "true")
    private var _3_withSelect: Boolean = false

//    @Param("1", "2", "4") // local machine
//    @Param("1", "2", "4", "8", "12") // local machine
    @Param("1", "2", "4", "8", "16", "32", "64", "128", "144") // dasquad
//    @Param("1", "2", "4", "8", "16", "32", "64", "96") // Google Cloud
    private var _4_parallelism: Int = 0

    private lateinit var dispatcher: CoroutineDispatcher
    private lateinit var channel: Channel<Int>

    @InternalCoroutinesApi
    @Setup
    fun setup() {
        dispatcher = _0_dispatcher.create(_4_parallelism)
        channel = _1_channel.create()
    }

    @Benchmark
    fun scmp() {
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
        val n = APPROX_BATCH_SIZE / producers * producers
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
            val channel = this.channel
            when (channel) {
                is RendezvousChannelMSQueue -> {
                    channel.receive()
                }
                is RendezvousChannelEuropar<Int> -> {
                    dummy as RendezvousChannelEuropar<Int>
                    selectEuropar<Unit> {
                        channel.onSendEuropar(element) {}
                        dummy.onReceiveEuropar {}
                    }
                }
                is BufferedChannel<Int> -> {
                    dummy as BufferedChannel<Int>
                    newSelect<Unit> {
                        channel.onSendNew(element) {}
                        dummy.onReceiveNew { }
                    }
                }
                else -> {
                    select<Unit> {
                        channel.onSend(element) {}
                        dummy!!.onReceive {}
                    }
                }
            }
        } else {
            channel.send(element)
        }
        doWork()
    }

    private suspend fun consume(dummy: Channel<Int>?) {
        if (_3_withSelect) {
            val channel = this.channel
            when (channel) {
                is RendezvousChannelMSQueue -> {
                    channel.receive()
                }
                is RendezvousChannelEuropar<Int> -> {
                    dummy as RendezvousChannelEuropar<Int>
                    selectEuropar<Unit> {
                        channel.onReceiveEuropar {}
                        dummy.onReceiveEuropar {}
                    }
                }
                is BufferedChannel<Int> -> {
                    dummy as BufferedChannel<Int>
                    newSelect<Unit> {
                        channel.onReceiveNew {}
                        dummy.onReceiveNew { }
                    }
                }
                else -> {
                    select<Unit> {
                        channel.onReceive {}
                        dummy!!.onReceive {}
                    }
                }
            }
        } else {
            channel.receive()
        }
        doWork()
    }
}

enum class DispatcherCreator(val create: (parallelism: Int) -> CoroutineDispatcher) {
//    FORK_JOIN({ parallelism ->  ForkJoinPool(parallelism).asCoroutineDispatcher() }),
    DEFAULT({ parallelism -> ExperimentalCoroutineDispatcher(corePoolSize = parallelism, maxPoolSize = parallelism) })
}

enum class ChannelCreator(val create: () -> Channel<Int>) {
    KOTLIN_RENDEZVOUS({ Channel(Channel.RENDEZVOUS) } ),
    KOTLIN_BUFFERED_64({ Channel(64) } ),
    KOVAL_RENDEZVOUS({ RendezvousChannelEuropar() } ),
    MSQUEUE_RENDEZVOUS({ RendezvousChannelMSQueue() } ),
    BUFFERED_RENDEZVOUS({ BufferedChannel(Channel.RENDEZVOUS) } ),
    BUFFERED_BUFFERED_64({ BufferedChannel(64) } )
}

private fun doWork(): Unit = Blackhole.consumeCPU(ThreadLocalRandom.current().nextLong(WORK_MIN, WORK_MAX))

private const val WORK_MIN = 50L
private const val WORK_MAX = 100L
private const val APPROX_BATCH_SIZE = 100000
