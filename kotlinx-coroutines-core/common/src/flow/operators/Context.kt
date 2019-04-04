/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.coroutines.*
import kotlin.jvm.*
import kotlinx.coroutines.flow.unsafeFlow as flow

/**
 * The operator that changes the context where this flow is executed to the given [flowContext].
 * This operator is composable and affects only precedent operators that do not have its own context.
 * This operator is pure: [flowContext] **does not** leak into the downstream flow.
 *
 * For example:
 * ```
 * val singleValue = intFlow // will be executed on IO if context wasn't specified before
 *     .map { ... } // Will be executed in IO
 *     .flowOn(Dispatchers.IO)
 *     .filter { ... } // Will be executed in Default
 *     .flowOn(Dispatchers.Default)
 *     .single() // Will be executed in the context of the caller
 * ```
 * For more explanation of purity concept please refer to [Flow] documentation.
 *
 * This operator uses a channel of the specific [bufferSize] in order to switch between contexts,
 * but it is not guaranteed that the channel will be created, implementation is free to optimize it away in case of fusing.
 *
 * @throws [IllegalStateException] if provided context contains [Job] instance.
 */
@FlowPreview
public fun <T> Flow<T>.flowOn(flowContext: CoroutineContext, bufferSize: Int = 16): Flow<T> {
    check(flowContext, bufferSize)
    return flow {
        // Fast-path, context is not changed, so we can just fallback to plain collect
        val currentContext = coroutineContext.minusKey(Job) // Jobs are ignored
        if (flowContext == currentContext) {
            collect { value -> emit(value) }
            return@flow
        }

        coroutineScope {
            val channel = produce(flowContext, capacity = bufferSize) {
                collect { value ->
                    send(value)
                }
            }

            // TODO semantics doesn't play well here and we pay for that with additional object
             (channel as Job).invokeOnCompletion { if (it is CancellationException && it.cause == null) cancel() }
            for (element in channel) {
                emit(element)
            }

            val producer = channel as Job
            if (producer.isCancelled) {
                producer.join()
                throw producer.getCancellationException()
            }
        }
    }
}

/**
 * The operator that changes the context where all transformations applied to the given flow within a [builder] are executed.
 * This operator is pure and does not affect the context of the precedent and subsequent operations.
 *
 * Example:
 * ```
 * flow // not affected
 *     .map { ... } // Not affected
 *     .flowWith(Dispatchers.IO) {
 *         map { ... } // in IO
 *         .filter { ... } // in IO
 *     }
 *     .map { ... } // Not affected
 * ```
 * For more explanation of purity concept please refer to [Flow] documentation.
 *
 * This operator uses channel of the specific [bufferSize] in order to switch between contexts,
 * but it is not guaranteed that channel will be created, implementation is free to optimize it away in case of fusing.
 *
 * @throws [IllegalStateException] if provided context contains [Job] instance.
 */
@FlowPreview
public fun <T, R> Flow<T>.flowWith(
    flowContext: CoroutineContext,
    bufferSize: Int = 16,
    builder: Flow<T>.() -> Flow<R>
): Flow<R> {
    check(flowContext, bufferSize)
    val source = this
    return flow {
        /**
         * Here we should subtract Job instance from the context.
         * All builders are written using scoping and no global coroutines are launched, so it is safe not to provide explicit Job.
         * It is also necessary not to mess with cancellations if multiple flowWith are used.
         */
        val originalContext = coroutineContext.minusKey(Job)
        val prepared = source.flowOn(originalContext, bufferSize)
        builder(prepared).flowOn(flowContext, bufferSize).collect { value ->
            emit(value)
        }
    }
}

private fun check(flowContext: CoroutineContext, bufferSize: Int) {
    require(flowContext[Job] == null) {
        "Flow context cannot contain job in it. Had $flowContext"
    }

    require(bufferSize >= 0) {
        "Buffer size should be positive, but was $bufferSize"
    }
}
