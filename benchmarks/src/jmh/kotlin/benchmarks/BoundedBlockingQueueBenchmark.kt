/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks

import benchmarks.common.*
import kotlinx.coroutines.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*
import kotlin.concurrent.*

@Warmup(iterations = 2, time = 500, timeUnit = TimeUnit.MILLISECONDS)
@Measurement(iterations = 5, time = 500, timeUnit = TimeUnit.MILLISECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.Throughput)
@OutputTimeUnit(TimeUnit.SECONDS)
@State(Scope.Benchmark)
open class BoundedBlockingQueueBenchmark {
    @Param("1", "2", "4", "8", "16", "32", "64", "128")
//    @Param("4", "8", "16", "128")
//    @Param("1", "16")
    var capacity: Int = 0

//    @Param("2", "128")
    @Param("2", "4", "8", "16", "32", "64", "128")
//    @Param("2", "4", "8")
    var threads: Int = 0

    @Param
    var algo: BCQAlgo = BCQAlgo.values()[0]

//    @Param("300")
    @Param("100", "200", "300", "500", "1000")
    var work: Int = 0

    lateinit var q: BoundedBlockingQueue<String>

    @Setup(Level.Invocation)
    fun setup() {
        q = algo.create(capacity)
    }

    @Benchmark
    fun spmc() {
        val producers = 1
        val consumers = Integer.max(1, threads - 1)
        run(producers, consumers)
    }

    @Benchmark
    fun mpsc() {
        val consumers = 1
        val producers = Integer.max(1, threads - 1)
        run(producers, consumers)
    }

    @Benchmark
    fun mpmc() {
        val producers = (threads + 1) / 2
        val consumers = producers
        run(producers, consumers)
    }

    private fun run(producers: Int, consumers: Int) {
        val n = APPROX_BATCH_SIZE / producers * producers / consumers * consumers
        val phaser = Phaser(producers + consumers + 1)
        // Run producers
        repeat(producers) {
            thread {
                repeat(n / producers) {
                    q.send(VALUES[it])
                    doGeomDistrWork(work)
                }
                phaser.arrive()
            }
        }
        // Run consumers
        repeat(consumers) {
            thread {
                repeat(n / consumers) {
                    q.receive()
                    doGeomDistrWork(work)
                }
                phaser.arrive()
            }
        }
        // Wait until work is done
        phaser.arriveAndAwaitAdvance()
    }
}

@Warmup(iterations = 2, time = 500, timeUnit = TimeUnit.MILLISECONDS)
@Measurement(iterations = 5, time = 500, timeUnit = TimeUnit.MILLISECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.Throughput)
@OutputTimeUnit(TimeUnit.SECONDS)
@State(Scope.Benchmark)
open class SequentialBoundedBlockingQueueBenchmark {
    @Param("1", "2", "4", "8", "16", "32", "64", "128")
//    @Param("4", "8", "16", "128")
//    @Param("1", "16")
    var capacity: Int = 0

    @Param
    var algo: BCQAlgo = BCQAlgo.values()[0]

//    @Param("100")
    @Param("100", "200", "300", "500", "1000")
    var work: Int = 0

    @Benchmark
    fun benchmark() {
        val q = algo.create(capacity)
        var i = 0
        while (true) {
            repeat(capacity) {
                q.send(VALUES[i])
                doGeomDistrWork(work)
                if (++i == APPROX_BATCH_SIZE) return
            }
            repeat(capacity) {
                q.receive()
                doGeomDistrWork(work)
                if (++i == APPROX_BATCH_SIZE) return
            }
        }
    }
}

private const val APPROX_BATCH_SIZE = 100_000
private val VALUES = (0 until APPROX_BATCH_SIZE).map { "$it" }

@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE", "INVISIBLE_OVERRIDE", "CANNOT_OVERRIDE_INVISIBLE_MEMBER")
enum class BCQAlgo(val create: (capacity: Int) -> BoundedBlockingQueue<String>) {
    JAVA_ARRAY_FAIR({ArrayBlockingQueueJava(it, true)}),
    JAVA_ARRAY_UNFAIR({ArrayBlockingQueueJava(it, false)}),
    JAVA_LINKED({LinkedBlockingQueueJava(it)}),

    SIMPLE_ARRAY_FAIR({BoundedBlockingQueueSimpleArray(it, true)}),
    SIMPLE_ARRAY_UNFAIR({BoundedBlockingQueueSimpleArray(it, false)}),
    SIMPLE_QUEUE_FAIR({BoundedBlockingQueueSimpleQueue(it, true)}),
    SIMPLE_QUEUE_UNFAIR({BoundedBlockingQueueSimpleQueue(it, false)}),

    SMART_ARRAY_FAIR({BoundedBlockingQueueSmartArray(it, true)}),
    SMART_ARRAY_UNFAIR({BoundedBlockingQueueSmartArray(it, false)}),
    SMART_QUEUE_FAIR({BoundedBlockingQueueSmartQueue(it, true)}),
    SMART_QUEUE_UNFAIR({BoundedBlockingQueueSmartQueue(it, false)}),
}