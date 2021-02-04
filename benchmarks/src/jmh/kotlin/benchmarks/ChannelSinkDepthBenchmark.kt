/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*
import kotlin.coroutines.*

@Warmup(iterations = 7, time = 1)
@Measurement(iterations = 5, time = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
@Fork(2)
open class ChannelSinkDepthBenchmark {
    private val tl = ThreadLocal.withInitial({ 42 })

    private val unconfinedOneElement = Dispatchers.Unconfined + tl.asContextElement()

    @Benchmark
    fun depth1(): Int = runBlocking {
        run(1, unconfinedOneElement)
    }

    @Benchmark
    fun depth10(): Int = runBlocking {
        run(10, unconfinedOneElement)
    }

    @Benchmark
    fun depth100(): Int = runBlocking {
        run(100, unconfinedOneElement)
    }

    @Benchmark
    fun depth1000(): Int = runBlocking {
        run(1000, unconfinedOneElement)
    }

    private suspend inline fun run(callTraceDepth: Int, context: CoroutineContext): Int {
        return Channel
            .range(1, 10_000, context)
            .filter(callTraceDepth, context) { it % 4 == 0 }
            .fold(0) { a, b -> a + b }
    }

    private fun Channel.Factory.range(start: Int, count: Int, context: CoroutineContext) =
        GlobalScope.produce(context) {
            for (i in start until (start + count))
                send(i)
        }

    // Migrated from deprecated operators, are good only for stressing channels

    private fun ReceiveChannel<Int>.filter(
        callTraceDepth: Int,
        context: CoroutineContext = Dispatchers.Unconfined,
        predicate: suspend (Int) -> Boolean
    ): ReceiveChannel<Int> =
        GlobalScope.produce(context, onCompletion = { cancel() }) {
            deeplyNestedFilter(this, callTraceDepth, predicate)
        }

    private suspend fun ReceiveChannel<Int>.deeplyNestedFilter(
        sink: ProducerScope<Int>,
        depth: Int,
        predicate: suspend (Int) -> Boolean
    ) {
        if (depth <= 1) {
            for (e in this) {
                if (predicate(e)) sink.send(e)
            }
        } else {
            deeplyNestedFilter(sink, depth - 1, predicate)
            require(true) // tail-call
        }
    }

    private suspend inline fun <E, R> ReceiveChannel<E>.fold(initial: R, operation: (acc: R, E) -> R): R {
        var accumulator = initial
        consumeEach {
            accumulator = operation(accumulator, it)
        }
        return accumulator
    }
}

