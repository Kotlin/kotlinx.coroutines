/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*
import kotlin.coroutines.*

@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 5, time = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
@Fork(1)
open class ChannelSinkBenchmark {
    private val tl = ThreadLocal.withInitial({ 42 })
    private val tl2 = ThreadLocal.withInitial({ 239 })

    private val unconfined = Dispatchers.Unconfined
    private val unconfinedOneElement = Dispatchers.Unconfined + tl.asContextElement()
    private val unconfinedTwoElements = Dispatchers.Unconfined + tl.asContextElement() + tl2.asContextElement()

    @Benchmark
    fun channelPipeline(): Int = runBlocking {
        run(unconfined)
    }

    @Benchmark
    fun channelPipelineOneThreadLocal(): Int = runBlocking {
        run(unconfinedOneElement)
    }

    @Benchmark
    fun channelPipelineTwoThreadLocals(): Int = runBlocking {
        run(unconfinedTwoElements)
    }

    private suspend inline fun run(context: CoroutineContext): Int {
        return Channel
            .range(1, 1_000_000, context)
            .filter(context) { it % 4 == 0 }
            .fold(0) { a, b -> a + b }
    }

    private fun Channel.Factory.range(start: Int, count: Int, context: CoroutineContext) = GlobalScope.produce(context) {
        for (i in start until (start + count))
            send(i)
    }

    // Migrated from deprecated operators, are good only for stressing channels

    private fun <E> ReceiveChannel<E>.filter(context: CoroutineContext = Dispatchers.Unconfined, predicate: suspend (E) -> Boolean): ReceiveChannel<E> =
        GlobalScope.produce(context, onCompletion = { cancel() }) {
            for (e in this@filter) {
                if (predicate(e)) send(e)
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

