/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*
import kotlin.coroutines.*

@Warmup(iterations = 3, time = 1)
@Measurement(iterations = 5, time = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
@Fork(1)
open class ChannelSinkNoAllocationsBenchmark {
    private val unconfined = Dispatchers.Unconfined

    @Benchmark
    fun channelPipeline(): Int = runBlocking {
        run(unconfined)
    }

    private suspend inline fun run(context: CoroutineContext): Int {
        var size = 0
        Channel.range(context).consumeEach { size++ }
        return size
    }

    private fun Channel.Factory.range(context: CoroutineContext) = GlobalScope.produce(context) {
        for (i in 0 until 100_000)
            send(Unit) // no allocations
    }
}
