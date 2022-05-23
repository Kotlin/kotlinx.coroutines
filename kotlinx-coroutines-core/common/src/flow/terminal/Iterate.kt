/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*

/**
 * Iterator for [Flow]. Instances of this interface are only usable within calls to `flow.iterate`.
 * They are not thread-safe and should not be used from concurrent coroutines.
 */
interface FlowIterator<T> {
    /**
     * Returns `true` if there is another element in the flow, or `false` if the flow completes normally.
     * If the flow fails exceptionally, throws that exception.
     *
     * This function suspends until the backing flow either emits an element or completes.
     */
    operator suspend fun hasNext(): Boolean

    /**
     * Returns the next element in the flow, or throws `NoSuchElementException` if the flow completed normally without
     * emitting another element.  If the flow failed exceptionally, throws that exception.
     *
     * This function does not suspend if `hasNext()` has already been called since the last call to `next`.
     * Otherwise, it suspends until the backing flow either emits an element or completes.
     */
    operator suspend fun next(): T
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
suspend fun <T, R> Flow<T>.iterate(block: FlowIterator<T>.() -> R): R = coroutineScope {
    // Instead of a channel-based approach, we pass continuations back and forth between the collector and the
    // iterator.

    val firstCont = CompletableDeferred<CancellableContinuation<ContToken<T>>>()
    val collectorJob = launch {
        var tokenCont = firstCont.await()
        onCompletion { thrown ->
            suspendCancellableContinuation { collectionCont ->
                tokenCont.resume(ContToken(ChannelResult.closed(thrown), collectionCont))
            }
        }.collect { elem ->
            tokenCont = suspendCancellableContinuation { collectionCont ->
                tokenCont.resume(ContToken(ChannelResult.success(elem), collectionCont))
            }
        }
    }
    var usable = true
    val itr = object : FlowIterator<T> {
        private var next = ChannelResult.failure<T>()
        private var collectionCont: CancellableContinuation<ContToken<T>>? = null

        override suspend fun hasNext(): Boolean {
            check(usable) { "FlowIterator is only usable within the body of the corresponding iterate call" }
            if (next.isFailure && !next.isClosed) {
                val (theNext, theCollectionCont) = suspendCancellableCoroutine { tokenCont ->
                    // collectorJob is waiting for tokenCont.  Pass tokenCont to it and suspend until it replies
                    // with a ChannelResult/element-or-termination and a continuation.
                    when (val theCollectionCont = collectionCont) {
                        null -> firstCont.complete(tokenCont)
                        else -> theCollectionCont.resume(tokenCont)
                    }
                }
                next = theNext
                collectionCont = theCollectionCont
            }

            // next should never be failed now
            return if (next.isSuccess) {
                true
            } else {
                val ex = next.exceptionOrNull()
                if (ex == null) {
                    false
                } else {
                    throw ex
                }
            }
        }

        override suspend fun next(): T {
            if (!hasNext()) {
                throw NoSuchElementException("No next element")
            }
            return next.getOrThrow().also { next = ChannelResult.failure()}
        }
    }
    try {
        block(itr)
    } finally {
        usable = false
        collectorJob.cancel(CancellationException("early return from Flow.iterate"))
        // we don't actually want to close the channel, just let it die from leaving scope
    }
}

private class ContToken<T>(val nextValue: ChannelResult<T>, val resumption: CancellableContinuation<CancellableContinuation<ContToken<T>>>)