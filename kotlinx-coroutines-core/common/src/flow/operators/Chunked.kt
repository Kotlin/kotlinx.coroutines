/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.internal.*
import kotlinx.coroutines.selects.*
import kotlin.jvm.*
import kotlin.math.*
import kotlin.time.*

private const val NO_MAXIMUM = -1

public fun <T> Flow<T>.chunked(maxSize: Int, minSize: Int = 1): Flow<List<T>> {
    require(minSize in 0 until maxSize)
    return flow {
        val accumulator = mutableListOf<T>()
        collect { value ->
            accumulator.add(value)
            if (accumulator.size == maxSize) emit(accumulator.drain())
        }
        if (accumulator.size >= minSize) emit(accumulator)
    }
}

@ExperimentalTime
public fun <T> Flow<T>.chunked(
    chunkDuration: Duration,
    minSize: Int = 1,
    maxSize: Int = NO_MAXIMUM
): Flow<List<T>> = chunked(chunkDuration.toDelayMillis(), minSize, maxSize)

public fun <T> Flow<T>.chunked(
    chunkDurationMs: Long,
    minSize: Int = 1,
    maxSize: Int = NO_MAXIMUM
): Flow<List<T>> {
    require(chunkDurationMs > 0)
    require(minSize >= 0)
    require(maxSize == NO_MAXIMUM || maxSize >= minSize)

    return if (minSize == 0 && maxSize == NO_MAXIMUM) chunkFixedTimeWindows(chunkDurationMs)
    else if (minSize == 0) chunkContinousWindows(chunkDurationMs, maxSize)
    else chunkFloatingWindows(chunkDurationMs, minSize, maxSize)
}

public fun <T> Flow<T>.chunkFixedTimeWindows(durationMs: Long): Flow<List<T>> = scopedFlow { downstream ->
    val upstream = produce(capacity = Channel.CHANNEL_DEFAULT_CAPACITY) {
        val ticker = Ticker(durationMs, this).apply { send(Ticker.Message.Start) }
        launch {
            for (tick in ticker) send(Signal.TimeIsUp)
        }
        collect { value -> send(Signal.NewElement(value)) }
        ticker.close()
    }
    val accumulator = mutableListOf<T>()

    for (signal in upstream) {
        when (signal) {
            is Signal.NewElement -> accumulator.add(signal.value)
            is Signal.TimeIsUp -> downstream.emit(accumulator.drain())
        }
    }
    if (accumulator.isNotEmpty()) downstream.emit(accumulator)
}

public fun <T> Flow<T>.chunkContinousWindows(durationMs: Long, maxSize: Int): Flow<List<T>> =
    scopedFlow { downstream ->
        val inbox: ReceiveChannel<T> = this@chunkContinousWindows.produceIn(this)
        val ticker = Ticker(durationMs, this).apply { send(Ticker.Message.Start) }
        val accumulator = mutableListOf<T>()

        whileSelect {
            inbox.onReceiveOrClosed.invoke { valueOrClosed ->
                val isOpen = !valueOrClosed.isClosed
                if (isOpen) {
                    accumulator.add(valueOrClosed.value)
                    if(accumulator.size == maxSize){
                        ticker.send(Ticker.Message.Reset)
                        downstream.emit(accumulator.drain())
                        ticker.send(Ticker.Message.Start)
                    }
                }
                isOpen
            }
            ticker.onReceive.invoke {
                downstream.emit(accumulator.drain())
                true
            }
        }

        ticker.close()
        if (accumulator.isNotEmpty()) downstream.emit(accumulator)
    }

public fun <T> Flow<T>.chunkFloatingWindows(
    durationMs: Long,
    minSize: Int,
    maxSize: Int,
): Flow<List<T>> {

    return scopedFlow { downstream ->
        val upstream: ReceiveChannel<T> = this@chunkFloatingWindows.produceIn(this)
        val ticker = Ticker(durationMs, this)
        val accumulator = mutableListOf<T>()

        whileSelect {
            upstream.onReceiveOrClosed.invoke { valueOrClosed ->
                val isOpen = valueOrClosed.isClosed.not()
                if (isOpen) {
                    if (accumulator.isEmpty()) ticker.send(Ticker.Message.Start)
                    accumulator.add(valueOrClosed.value)
                    if (accumulator.size == maxSize) {
                        ticker.send(Ticker.Message.Reset)
                        downstream.emit(accumulator.drain())
                    }
                }
                isOpen
            }
            ticker.onReceive.invoke {
                if (accumulator.size >= minSize) downstream.emit(accumulator.drain())
                true
            }
        }

        ticker.close()
        if (accumulator.size >= minSize) downstream.emit(accumulator)
    }
}

private class Ticker(
    private val intervalMs: Long,
    scope: CoroutineScope,
    private val inbox: Channel<Message> = Channel(),
    private val ticks: Channel<Unit> = Channel()
) : SendChannel<Ticker.Message> by inbox, ReceiveChannel<Unit> by ticks {

    init {
        scope.processMessages()
    }

    private fun CoroutineScope.processMessages() = launch {
        var ticker = setupTicks()
        for (message in inbox) {
            when (message) {
                Message.Start -> ticker.start()
                Message.Reset -> {
                    ticker.cancel()
                    ticker = setupTicks()
                }
            }
        }
        ticker.cancel()
        ticks.cancel()
    }

    private fun CoroutineScope.setupTicks() = launch(start = CoroutineStart.LAZY) {
        while (true) {
            delay(intervalMs)
            ticks.send(Unit)
        }
    }

    sealed class Message {
        object Start : Message()
        object Reset : Message()
    }
}

private sealed class Signal<out T> {
    class NewElement<out T>(val value: T) : Signal<T>()
    object TimeIsUp : Signal<Nothing>()
}

private fun <T> MutableList<T>.drain() = toList().also { this.clear() }