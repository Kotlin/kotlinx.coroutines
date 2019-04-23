/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.internal.*
import kotlin.coroutines.*
import kotlin.jvm.*

/**
 * Creates flow from the given suspendable [block].
 *
 * Example of usage:
 * ```
 * fun fibonacci(): Flow<Long> = flow {
 *     emit(1L)
 *     var f1 = 1L
 *     var f2 = 1L
 *     repeat(100) {
 *         var tmp = f1
 *         f1 = f2
 *         f2 += tmp
 *         emit(f1)
 *     }
 * }
 * ```
 *
 * `emit` should happen strictly in the dispatchers of the [block] in order to preserve flow context.
 * For example, the following code will produce [IllegalStateException]:
 * ```
 * flow {
 *     emit(1) // Ok
 *     withContext(Dispatcher.IO) {
 *         emit(2) // Will fail with ISE
 *     }
 * }
 * ```
 * If you want to switch the context where this flow is executed use [flowOn] operator.
 */
@FlowPreview
public fun <T> flow(@BuilderInference block: suspend FlowCollector<T>.() -> Unit): Flow<T> {
    return object : Flow<T> {
        override suspend fun collect(collector: FlowCollector<T>) {
            SafeCollector(collector, coroutineContext).block()
        }
    }
}

/**
 * Analogue of [flow] builder that does not check a context of flow execution.
 * Used in our own operators where we trust the context of the invocation.
 */
@FlowPreview
@PublishedApi
internal fun <T> unsafeFlow(@BuilderInference block: suspend FlowCollector<T>.() -> Unit): Flow<T> {
    return object : Flow<T> {
        override suspend fun collect(collector: FlowCollector<T>) {
            collector.block()
        }
    }
}

/**
 * Creates flow that produces single value from the given functional type.
 */
@FlowPreview
public fun <T> (() -> T).asFlow(): Flow<T> = unsafeFlow {
    emit(invoke())
}

/**
 * Creates flow that produces single value from the given functional type.
 */
@FlowPreview
public fun <T> (suspend () -> T).asFlow(): Flow<T> = unsafeFlow {
    emit(invoke())
}

/**
 * Creates flow that produces values from the given iterable.
 */
@FlowPreview
public fun <T> Iterable<T>.asFlow(): Flow<T> = unsafeFlow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates flow that produces values from the given iterable.
 */
@FlowPreview
public fun <T> Iterator<T>.asFlow(): Flow<T> = unsafeFlow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates flow that produces values from the given sequence.
 */
@FlowPreview
public fun <T> Sequence<T>.asFlow(): Flow<T> = unsafeFlow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates flow that produces values from the given array of elements.
 */
@FlowPreview
public fun <T> flowOf(vararg elements: T): Flow<T> = unsafeFlow {
    for (element in elements) {
        emit(element)
    }
}

/**
 * Returns an empty flow.
 */
@FlowPreview
public fun <T> emptyFlow(): Flow<T> = EmptyFlow

private object EmptyFlow : Flow<Nothing> {
    override suspend fun collect(collector: FlowCollector<Nothing>) = Unit
}

/**
 * Creates flow that produces values from the given array.
 */
@FlowPreview
public fun <T> Array<T>.asFlow(): Flow<T> = flow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates flow that produces values from the given array.
 */
@FlowPreview
public fun IntArray.asFlow(): Flow<Int> = flow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates flow that produces values from the given array.
 */
@FlowPreview
public fun LongArray.asFlow(): Flow<Long> = flow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates flow that produces values from the given range.
 */
@FlowPreview
public fun IntRange.asFlow(): Flow<Int> = flow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates flow that produces values from the given range.
 */
@FlowPreview
public fun LongRange.asFlow(): Flow<Long> = flow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates an instance of the cold [Flow] with elements that are sent to a [SendChannel]
 * that is provided to the builder's [block] of code. It allows elements to be
 * produced by the code that is running in a different context, e.g. from a callback-based API.
 *
 * The resulting flow is _cold_, which means that [block] is called on each call of a terminal operator
 * on the resulting flow. The [block] is not suspending deliberately, if you need suspending scope, [flow] builder
 * should be used instead.
 *
 * To control backpressure, [bufferSize] is used and matches directly the `capacity` parameter of [Channel] factory.
 * The provided channel can later be used by any external service to communicate with flow and its buffer determines
 * backpressure buffer size or its behaviour (e.g. in case when [Channel.CONFLATED] was used).
 *
 * Example of usage:
 * ```
 * fun flowFrom(api: CallbackBasedApi): Flow<T> = flowViaChannel { channel ->
 *     val callback = object : Callback { // implementation of some callback interface
 *         override fun onNextValue(value: T) {
 *             channel.offer(value) // Note: offer drops value when buffer is full
 *         }
 *         override fun onApiError(cause: Throwable) {
 *             channel.cancel("API Error", CancellationException(cause))
 *         }
 *         override fun onCompleted() = channel.close()
 *     }
 *     api.register(callback)
 *     channel.invokeOnClose {
 *         api.unregister(callback)
 *     }
 * }
 * ```
 */
@FlowPreview
public fun <T> flowViaChannel(
    bufferSize: Int = 16,
    @BuilderInference block: CoroutineScope.(channel: SendChannel<T>) -> Unit
): Flow<T> {
    return flow {
        coroutineScope {
            val channel = Channel<T>(bufferSize)
            launch {
                block(channel)
            }

            channel.consumeEach { value ->
                emit(value)
            }
        }
    }
}
