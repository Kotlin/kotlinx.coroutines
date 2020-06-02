/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.common

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.selects.*
import java.util.concurrent.*

/**
 * Runs a batch send-receive pairs under the specified workload.
 */
public abstract class ChannelProdConsBenchmarkIteration(
    private val channelCreator: ChannelCreator,
    private val withSelect: Boolean,
    private val producers: Int,
    private val consumers: Int,
    dispatcherCreator: DispatcherCreator,
    parallelism: Int,
    approximateBatchSize: Int
) {
    public val totalMessages: Int = approximateBatchSize / (producers * consumers) * (producers * consumers)

    private val channel: Channel<Int> = channelCreator.create()
    private val dispatcher = dispatcherCreator.create(parallelism)

    public fun run() {
        val phaser = Phaser(producers + consumers + 1)
        // Run producers
        repeat(producers) { coroutineNumber ->
            GlobalScope.launch(dispatcher) {
                val dummy = if (withSelect) channelCreator.create() else null
                repeat(totalMessages / producers) {
                    produce(it, dummy, coroutineNumber)
                }
                phaser.arrive()
            }
        }
        // Run consumers
        repeat(consumers) { coroutineNumber ->
            GlobalScope.launch(dispatcher) {
                val dummy = if (withSelect) channelCreator.create() else null
                repeat(totalMessages / consumers) {
                    consume(dummy, coroutineNumber)
                }
                phaser.arrive()
            }
        }
        // Wait until the work is done
        phaser.arriveAndAwaitAdvance()
    }

    private suspend fun produce(element: Int, dummy: Channel<Int>?, coroutineNumber: Int) {
        if (withSelect) {
            select<Unit> {
                channel.onSend(element) {}
                dummy!!.onReceive {}
            }
        } else {
            channel.send(element)
        }
        doProducerWork(coroutineNumber)
    }

    private suspend fun consume(dummy: Channel<Int>?, coroutineNumber: Int) {
        if (withSelect) {
            select<Unit> {
                channel.onReceive {}
                dummy!!.onReceive {}
            }
        } else {
            channel.receive()
        }
        doConsumerWork(coroutineNumber)
    }

    public abstract fun doProducerWork(id: Int)
    public abstract fun doConsumerWork(id: Int)
}