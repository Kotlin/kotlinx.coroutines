/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlin.coroutines.*
import kotlin.jvm.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*

/**
 * Iterator for [Flow]. Instances of this interface are only usable within calls to `flow.iterate`.
 * They are not thread-safe and should not be used from concurrent coroutines.
 */
public interface FlowIterator<T> {
    /**
     * Returns `true` if there is another element in the flow, or `false` if the flow completes normally.
     * If the flow fails exceptionally, throws that exception.
     *
     * This function suspends until the backing flow either emits an element or completes.
     */
    public operator suspend fun hasNext(): Boolean

    /**
     * Returns the next element in the flow, or throws `NoSuchElementException` if the flow completed normally without
     * emitting another element.  If the flow failed exceptionally, throws that exception.
     *
     * This function does not suspend if `hasNext()` has already been called since the last call to `next`.
     * Otherwise, it suspends until the backing flow either emits an element or completes.
     */
    public operator suspend fun next(): T
}

/**
 * Collects this flow, allowing it to be iterated through one element at a time.  For example,
 * instead of writing
 * ```
 * var even = true
 * flow.collect {
 *   if (even) {
 *     handleEven(it)
 *   } else {
 *     handleOdd(it)
 *   }
 *   even = !even
 * }
 * ```
 *
 * you might write
 * ```
 * flow.iterate { iter ->
 *   while (iter.hasNext()) {
 *     handleEven(iter.next())
 *     if (!iter.hasNext()) break
 *     handleOdd(iter.next())
 *   }
 * }
 * ```
 *
 * Flow collection is cancelled as soon as [block] returns a value:
 * ```
 * suspend fun <T> Flow<T>.all(predicate: (T) -> Boolean): Boolean = iterate { iter ->
 *   while (iter.hasNext()) {
 *     if (!predicate(iter.next())) return@iterate false // stops collecting the flow
 *   }
 *   true
 * }
 * ```
 *
 * The `FlowIterator` available to [block] is only usable within [block], and has undefined behavior
 * if used anywhere outside [block].  Additionally, the `FlowIterator` cannot be used concurrently
 * by multiple coroutines.
 */
public suspend fun <T, R> Flow<T>.iterate(block: suspend FlowIterator<T>.() -> R): R = coroutineScope {
    // Instead of a channel-based approach, we pass continuations back and forth between the collector and the
    // iterator.  This requires some nested continuations, but probably improves performance.
    var usable = true
    val itr = object : FlowIterator<T> {
        /**
         * A pure failure indicates the next value hasn't been determined yet.
         */
        private var next = ChannelResult.failure<T>()

        /**
         * The continuation to use to resume collection, passing it the continuation to resume the iterator
         * functions after the next element (or closure) is ready.
         */
        private var collectionCont: CancellableContinuation<CancellableContinuation<ContToken<T>>>? = null
        var collectorJob: Job? = null
        private var iteratorJob: Job? = null

        override suspend fun hasNext(): Boolean {
            check(usable) { "FlowIterator is only usable ithin the body of the corresponding iterate call" }
            if (next.isFailure && !next.isClosed) {
                if (iteratorJob == null) {
                    iteratorJob = coroutineContext[Job]
                } else {
                    check(iteratorJob === coroutineContext[Job]) {
                        "FlowIterator is not thread-safe and cannot be used from multiple coroutines."
                    }
                }
                val (theNext, theCollectionCont) = suspendCancellableCoroutine<ContToken<T>> { tokenCont ->
                    when (val theCollectionCont = collectionCont) {
                        null -> collectorJob = launch { doCollect(tokenCont) }
                        else -> theCollectionCont.resume(tokenCont)
                    }
                }
                next = theNext
                collectionCont = theCollectionCont
            }

            return if (next.isSuccess) {
                true
            } else {
                // assert(next.isClosed)
                val ex = next.exceptionOrNull()
                if (ex == null) {
                    false
                } else {
                    throw ex
                }
            }
        }

        private suspend fun doCollect(firstTokenCont: CancellableContinuation<ContToken<T>>) {
            var tokenCont = firstTokenCont
            onCompletion { thrown ->
                if (thrown !is CancellationException) {
                    // should never get used
                    tokenCont = suspendCancellableCoroutine { collectionCont ->
                        tokenCont.resume(
                            ContToken(
                                ChannelResult.closed(thrown),
                                collectionCont
                            )
                        )
                    }
                }
            }.collect { elem ->
                tokenCont = suspendCancellableCoroutine { collectionCont ->
                    tokenCont.resume(ContToken(ChannelResult.success(elem), collectionCont))
                }
            }
        }

        override suspend fun next(): T {
            if (!hasNext()) {
                throw NoSuchElementException("No next element")
            }
            // getOrThrow should always succeed at this point
            return next.getOrThrow().also {
                next = ChannelResult.failure()
            }
        }
    }
    try {
        block(itr)
    } finally {
        usable = false
        itr.collectorJob?.cancel("early return from Flow.iterate")
        // we don't actually want to close the channel, just let it die from leaving scope
    }
}

/** Pair of a [ChannelResult] and a continuation of a continuation. */
private data class ContToken<T>(
    val nextValue: ChannelResult<T>,
    val resumption: CancellableContinuation<CancellableContinuation<ContToken<T>>>
)