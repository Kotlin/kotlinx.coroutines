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
import kotlin.jvm.*
import kotlinx.coroutines.flow.unsafeFlow as flow

/**
 * Transforms elements emitted by the original flow by applying [transform], that returns another flow, and then concatenating and flattening these flows.
 * This method is identical to `flatMapMerge(concurrency = 1, bufferSize = 1)`
 *
 * Note that even though this operator looks very familiar, we discourage its usage in a regular application-specific flows.
 * Most likely, suspending operation in [map] operator will be sufficient and linear transformations are much easier to reason about.
 */
@FlowPreview
public fun <T, R> Flow<T>.flatMapConcat(transform: suspend (value: T) -> Flow<R>): Flow<R> = flow {
    collect { value ->
        transform(value).collect { innerValue ->
            emit(innerValue)
        }
    }
}

/**
 * Transforms elements emitted by the original flow by applying [transform], that returns another flow, and then merging and flattening these flows.
 *
 * Note that even though this operator looks very familiar, we discourage its usage in a regular application-specific flows.
 * Most likely, suspending operation in [map] operator will be sufficient and linear transformations are much easier to reason about.
 *
 * [bufferSize] parameter controls the size of backpressure aka the amount of queued in-flight elements.
 * [concurrency] parameter controls the size of in-flight flows, at most [concurrency] flows are collected at the same time.
 */
@FlowPreview
public fun <T, R> Flow<T>.flatMapMerge(concurrency: Int = 16, bufferSize: Int = 16, transform: suspend (value: T) -> Flow<R>): Flow<R> {
    require(bufferSize >= 0) { "Expected non-negative buffer size, but had $bufferSize" }
    require(concurrency >= 0) { "Expected non-negative concurrency level, but had $concurrency" }
    return flow {
        coroutineScope {
            val semaphore = Channel<Unit>(concurrency)
            val flatMap = SerializingFlatMapCollector(this@flow, bufferSize)
            collect { outerValue ->
                // TODO real semaphore (#94)
                semaphore.send(Unit) // Acquire concurrency permit
                val inner = transform(outerValue)
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
 * Flattens the given flow of flows into a single flow in a sequentially manner, without interleaving nested flows.
 * This method is identical to `flattenMerge(concurrency = 1, bufferSize = 1)
 */
@FlowPreview
public fun <T> Flow<Flow<T>>.flattenConcat(): Flow<T> = flow {
    collect { value ->
        value.collect { innerValue ->
            emit(innerValue)
        }
    }
}

/**
 * Flattens the given flow of flows into a single flow.
 * This method is identical to `flatMapMerge(concurrency, bufferSize) { it }`
 *
 * [bufferSize] parameter controls the size of backpressure aka the amount of queued in-flight elements.
 * [concurrency] parameter controls the size of in-flight flows, at most [concurrency] flows are collected at the same time.
 */
@FlowPreview
public fun <T> Flow<Flow<T>>.flattenMerge(concurrency: Int = 16, bufferSize: Int = 16): Flow<T> = flatMapMerge(concurrency, bufferSize) { it }

/**
 * Returns a flow that switches to a new flow produced by [transform] function every time the original flow emits a value.
 * When switch on the a flow is performed, the previous one is cancelled.
 *
 * For example, the following flow:
 * ```
 * flow {
 *     emit("a")
 *     delay(100)
 *     emit("b")
 * }.switchMap { value ->
 *     flow {
 *         emit(value + value)
 *         delay(200)
 *         emit(value + "_last")
 *     }
 * }
 * ```
 * produces `aa bb b_last`
 */
@FlowPreview
public fun <T, R> Flow<T>.switchMap(transform: suspend (value: T) -> Flow<R>): Flow<R> = flow {
    coroutineScope {
        var previousFlow: Job? = null
        collect { value ->
            // Linearize calls to emit as alternative to the channel. Bonus points for never-overlapping channels.
            previousFlow?.cancelAndJoin()
            // Undispatched to have better user experience in case of synchronous flows
            previousFlow = launch(start = CoroutineStart.UNDISPATCHED) {
                transform(value).collect { innerValue ->
                    emit(innerValue)
                }
            }
        }
    }
}

// Effectively serializes access to downstream collector from flatMap
private class SerializingFlatMapCollector<T>(
    private val downstream: FlowCollector<T>, bufferSize: Int
) {

    // Let's try to leverage the fact that flatMapMerge is never contended
    // TODO do not allocate channel
    private val channel = Channel<Any?>(bufferSize) // Should be any, but KT-30796
    private val inProgressLock = atomic(false)

    public suspend fun emit(value: T) {
        if (!inProgressLock.tryAcquire()) {
            channel.send(value ?: NULL)
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
            while (element != null) { // TODO receive or closed (#330)
                downstream.emit(NULL.unbox(element))
                element = channel.poll()
            }

            inProgressLock.release()
            // Enforce liveness
            if (channel.isEmpty || !inProgressLock.tryAcquire()) break
        }
    }
}

@Suppress("NOTHING_TO_INLINE")
private inline fun AtomicBoolean.tryAcquire(): Boolean = compareAndSet(false, true)

@Suppress("NOTHING_TO_INLINE")
private inline fun AtomicBoolean.release() {
    value = false
}
