/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks

import kotlinx.coroutines.channels.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

@Warmup(iterations = 5, time = 1000, timeUnit = TimeUnit.MILLISECONDS)
@Measurement(iterations = 10, time = 1000, timeUnit = TimeUnit.MILLISECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
open class TrivialChannelBenchmark {
    @Param
    private var algo: ChannelCreator = ChannelCreator.values()[0]
    private lateinit var c: Channel<String>

    private var contsForSend: List<Continuation<Unit>> = emptyList()
    private var contsForReceive: List<Continuation<String>> = emptyList()

    @Setup(Level.Invocation)
    fun setup() {
        c = algo.create()
        contsForSend = (1..N * 2).map { Continuation(EmptyCoroutineContext){} }
        contsForReceive = (1..N * 2).map { Continuation(EmptyCoroutineContext){} }
    }

    @Benchmark
    fun plain() {
        repeat(N) {
            c::send.startCoroutineUninterceptedOrReturn("$it", contsForSend[it])
        }
        repeat(2 * N) {
            c::receive.startCoroutineUninterceptedOrReturn(contsForReceive[it])
        }
        repeat(N) {
            c::send.startCoroutineUninterceptedOrReturn("$it", contsForSend[it])
        }
    }
}

private const val N = 1000