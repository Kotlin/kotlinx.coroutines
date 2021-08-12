/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks

import kotlinx.coroutines.channels.*
import kotlinx.coroutines.channels.koval_europar.*
import kotlinx.coroutines.selects.*
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
    private var algo: ChannelCreator = ChannelCreator.BUFFERED_BUFFERED_64
    private lateinit var c: Channel<Int>

    private var contsForSend: List<Continuation<Unit>> = emptyList()
    private var contsForReceive: List<Continuation<Int>> = emptyList()

    @Setup(Level.Invocation)
    fun setup() {
        c = algo.create()
        contsForSend = (1..N * 2).map { Continuation(EmptyCoroutineContext){} }
        contsForReceive = (1..N * 2).map { Continuation(EmptyCoroutineContext){} }
    }

    @Benchmark
    fun plain() {
        repeat(N) {
            c::send.startCoroutineUninterceptedOrReturn(it, contsForSend[it])
        }
        repeat(2 * N) {
            c::receive.startCoroutineUninterceptedOrReturn(contsForReceive[it])
        }
        repeat(N) {
            c::send.startCoroutineUninterceptedOrReturn(it, contsForSend[it])
        }
    }

    @Benchmark
    fun select() {
        repeat(N) {
            this::sendSelect.startCoroutineUninterceptedOrReturn(it, contsForSend[it])
        }
        repeat(2 * N) {
            this::receiveSelect.startCoroutineUninterceptedOrReturn(contsForReceive[it])
        }
        repeat(N) {
            this::sendSelect.startCoroutineUninterceptedOrReturn(it, contsForSend[it])
        }
    }

    suspend fun sendSelect(value: Int) {
        return when(val c = c) {
            is BufferedChannel<Int> -> {
                newSelect<Unit> { c.onSendNew(value){}  }
            }
            is RendezvousChannelEuropar<Int> -> {
                selectEuropar<Unit> { c.onSendEuropar(value){} }
            }
            is RendezvousChannelMSQueue<Int> -> return
            else -> {
                select<Unit> { c.onSend(value){} }
            }
        }
    }

    suspend fun receiveSelect(): Int {
        return when(val c = c) {
            is BufferedChannel<Int> -> {
                newSelect { c.onReceiveNew{ it }  }
            }
            is RendezvousChannelEuropar<Int> -> {
                selectEuropar { c.onReceiveEuropar{ it } }
            }
            is RendezvousChannelMSQueue<Int> -> -1
            else -> {
                select { c.onReceive{ it } }
            }
        }
    }
}

private const val N = 100