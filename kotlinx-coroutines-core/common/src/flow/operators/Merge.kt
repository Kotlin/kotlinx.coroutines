/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")
@file:Suppress("unused")

package kotlinx.coroutines.flow
import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.internal.*
import kotlinx.coroutines.flow.unsafeFlow as flow
import kotlin.jvm.*

/**
 * Transforms elements emitted by the original flow by applying [mapper], that returns another flow, and then merging and flattening these flows.
 *
 * Note that even though this operator looks very familiar, we discourage its usage in a regular application-specific flows.
 * Most likely, suspending operation in [map] operator will be sufficient and linear transformations are much easier to reason about.
 *
 * [bufferSize] parameter controls the size of backpressure aka the amount of queued in-flight elements.
 * [concurrency] parameter controls the size of in-flight flows.
 */
@FlowPreview
public fun <T, R> Flow<T>.flatMap(concurrency: Int = 16, bufferSize: Int = 16, mapper: suspend (value: T) -> Flow<R>): Flow<R> {
    return flow {
        val semaphore = Channel<Unit>(concurrency)
        val flatMap = SerializingFlatMapCollector(this, bufferSize)
        coroutineScope {
            collect { outerValue ->
                semaphore.send(Unit) // Acquire concurrency permit
                val inner = mapper(outerValue)
                launch {
                    try {
                        inner.collect { value ->
                            flatMap.emit(value)
                        }
                    } finally {
                        semaphore.receive() // Release concurrency permit
                    }
                }
            }
        }
    }
}

/**
 * Merges the given sequence of flows into a single flow with no guarantees on the order.
 *
 * [bufferSize] parameter controls the size of backpressure aka the amount of queued in-flight elements.
 * [concurrency] parameter controls the size of in-flight flows.
 */
@FlowPreview
public fun <T> Iterable<Flow<T>>.merge(concurrency: Int = 16, bufferSize: Int = 16): Flow<T> = asFlow().flatMap(concurrency, bufferSize) { it }

/**
 * Merges the given flow of flows into a single flow with no guarantees on the order.
 *
 * [bufferSize] parameter controls the size of backpressure aka the amount of queued in-flight elements.
 * [concurrency] parameter controls the size of in-flight flows.
 */
@FlowPreview
public fun <T> Flow<Flow<T>>.merge(concurrency: Int = 16, bufferSize: Int = 16): Flow<T> = flatMap(concurrency, bufferSize) { it }

/**
 * Concatenates values of each flow sequentially, without interleaving them.
 */
@FlowPreview
public fun <T> Flow<Flow<T>>.concatenate(): Flow<T> = flow {
    collect {
        val inner = it
        inner.collect { value ->
            emit(value)
        }
    }
}

/**
 * Transforms each value of the given flow into flow of another type and then flattens these flows
 * sequentially, without interleaving them.
 */
@FlowPreview
public fun <T, R> Flow<T>.concatenate(mapper: suspend (T) -> Flow<R>): Flow<R> = flow {
    collect { value ->
        mapper(value).collect { innerValue ->
            emit(innerValue)
        }
    }
}

// Effectively serializes access to downstream collector from flatMap
private class SerializingFlatMapCollector<T>(
    private val downstream: FlowCollector<T>,
    private val bufferSize: Int
) {

    // Let's try to leverage the fact that flatMap is never contended
    private val channel: Channel<Any?> by lazy { Channel<Any?>(bufferSize) } // Should be any, but KT-30796
    private val inProgressLock = atomic(false)
    private val sentValues = atomic(0)

    public suspend fun emit(value: T) {
        if (!inProgressLock.tryAcquire()) {
            sentValues.incrementAndGet()
            channel.send(value ?: NullSurrogate)
            if (inProgressLock.tryAcquire()) {
                helpEmit()
            }
            return
        }

        downstream.emit(value)
        helpEmit()
    }

    @Suppress("UNCHECKED_CAST")
    private suspend fun helpEmit() {
        while (true) {
            var element = channel.poll()
            while (element != null) { // TODO receive or closed
                if (element === NullSurrogate) downstream.emit(null as T)
                else downstream.emit(element as T)
                sentValues.decrementAndGet()
                element = channel.poll()
            }

            inProgressLock.release()
            // Enforce liveness of the algorithm
            // TODO looks like isEmpty use-case
            if (sentValues.value == 0 || !inProgressLock.tryAcquire()) break
        }
    }
}

private fun AtomicBoolean.tryAcquire(): Boolean = compareAndSet(false, true)

private fun AtomicBoolean.release() {
    value = false
}
