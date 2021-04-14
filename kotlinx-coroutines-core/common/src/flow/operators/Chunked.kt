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
import kotlin.time.*

public object ChunkConstraint {
    public const val NO_MAXIMUM: Int = Int.MAX_VALUE
    public const val NO_INTERVAL: Long = Long.MAX_VALUE
    public const val NATURAL_BATCHING: Long = 0
}

@ExperimentalTime
public fun <T> Flow<T>.chunked(
    interval: Duration,
    size: Int
): Flow<List<T>> = chunked(interval.toLongMilliseconds(), size)

public fun <T> Flow<T>.chunked(
    intervalMs: Long,
    size: Int
): Flow<List<T>> {
    require(intervalMs >= 0)
    require(size > 0)

    return chunkedTimeBased(intervalMs, size)
}

private fun <T> Flow<T>.chunkedTimeBased(intervalMs: Long, size: Int): Flow<List<T>> = scopedFlow { downstream ->
    val buffer = Channel<T>(size)
    val emitNowSemaphore = Channel<Unit>()

    launch {
        collect { value ->
            val hasCapacity = buffer.offer(value)
            if (!hasCapacity) {
                emitNowSemaphore.send(Unit)
                buffer.send(value)
            }
        }
        emitNowSemaphore.close()
        buffer.close()
    }

    whileSelect {
        emitNowSemaphore.onReceiveOrClosed { valueOrClosed ->
            buffer.drain(maxElements = size).takeIf { it.isNotEmpty() }?.let { downstream.emit(it) }
            valueOrClosed.isClosed.not()
        }
        onTimeout(intervalMs) {
            downstream.emit(buffer.awaitFirstAndDrain(maxElements = size))
            true
        }
    }
}

private suspend fun <T> ReceiveChannel<T>.awaitFirstAndDrain(maxElements: Int): List<T> {
    val first = receiveOrClosed().takeIf { it.isClosed.not() }?.value ?: return emptyList()
    return drain(mutableListOf(first), maxElements)
}

private tailrec fun <T> ReceiveChannel<T>.drain(acc: MutableList<T> = mutableListOf(), maxElements: Int): List<T> {
    val item = poll()
    return if (item == null || acc.size == maxElements) acc
    else {
        acc.add(item)
        drain(acc, maxElements)
    }
}

private fun <T> Flow<T>.chunkedSizeBased(size: Int): Flow<List<T>> = flow {
    val buffer = mutableListOf<T>()
    collect { value ->
        buffer.add(value)
        if (buffer.size == size) emit(buffer.drain())
    }
    if (buffer.isNotEmpty()) emit(buffer)
}

private fun <T> MutableList<T>.drain() = toList().also { this.clear() }