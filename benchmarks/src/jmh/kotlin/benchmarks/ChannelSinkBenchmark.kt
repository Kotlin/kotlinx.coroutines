/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*
import kotlin.coroutines.*

@Warmup(iterations = 10, time = 1)
@Measurement(iterations = 10, time = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
@Fork(2)
open class ChannelSinkBenchmark {

    @Benchmark
    fun channelPipeline(): Int = runBlocking {
        Channel
            .range(1, 1_000_000, Unconfined)
            .filter(Unconfined) { it % 4 == 0 }
            .fold(0) { a, b -> a + b }
    }

    private fun Channel.Factory.range(start: Int, count: Int, context: CoroutineContext) = produce(context) {
        for (i in start until (start + count))
            send(i)
    }
}
