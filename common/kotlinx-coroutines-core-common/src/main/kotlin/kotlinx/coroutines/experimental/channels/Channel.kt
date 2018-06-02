/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.CancellationException
import kotlinx.coroutines.experimental.CoroutineScope
import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.channels.Channel.Factory.CONFLATED
import kotlinx.coroutines.experimental.channels.Channel.Factory.UNLIMITED
import kotlinx.coroutines.experimental.selects.SelectClause1
import kotlinx.coroutines.experimental.selects.SelectClause2
import kotlinx.coroutines.experimental.selects.select
import kotlinx.coroutines.experimental.yield

/**
 * Sender's interface to [Channel].
 */
public interface SendChannel<in E> {
    /**
     * Returns `true` if this channel was closed by invocation of [close] and thus
     * the [send] and [offer] attempts throws exception.
     */
    public val isClosedForSend: Boolean

    /**
     * Returns `true` if the channel is full (out of capacity) and the [send] attempt will suspend.
     * This function returns `false` for [isClosedForSend] channel.
     */
    public val isFull: Boolean

    /**
     * Adds [element] into to this channel, suspending the caller while this channel [isFull],
     * or throws exception if the channel [isClosedForSend] (see [close] for details).
     *
     * Note, that closing a channel _after_ this function had suspended does not cause this suspended send invocation
     * to abort, because closing a channel is conceptually like sending a special "close token" over this channel.
     * All elements that are sent over the channel are delivered in first-in first-out order. The element that
     * is being sent will get delivered to receivers before a close token.
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this
     * function is suspended, this function immediately resumes with [CancellationException].
     *
     * *Cancellation of suspended send is atomic* -- when this function
     * throws [CancellationException] it means that the [element] was not sent to this channel.
     * As a side-effect of atomic cancellation, a thread-bound coroutine (to some UI thread, for example) may
     * continue to execute even after it was cancelled from the same thread in the case when this send operation
     * was already resumed and the continuation was posted for execution to the thread's queue.
     *
     * Note, that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     *
     * This function can be used in [select] invocation with [onSend] clause.
     * Use [offer] to try sending to this channel without waiting.
     */
    public suspend fun send(element: E)

    /**
     * Clause for [select] expression of [send] suspending function that selects when the element that is specified
     * as parameter is sent to the channel. When the clause is selected the reference to this channel
     * is passed into the corresponding block.
     *
     * The [select] invocation fails with exception if the channel [isClosedForSend] (see [close] for details).
     */
    public val onSend: SelectClause2<E, SendChannel<E>>

    /**
     * Adds [element] into this queue if it is possible to do so immediately without violating capacity restrictions
     * and returns `true`. Otherwise, it returns `false` immediately
     * or throws exception if the channel [isClosedForSend] (see [close] for details).
     */
    public fun offer(element: E): Boolean

    /**
     * Closes this channel with an optional exceptional [cause].
     * This is an idempotent operation -- repeated invocations of this function have no effect and return `false`.
     * Conceptually, its sends a special "close token" over this channel.
     *
     * Immediately after invocation of this function
     * [isClosedForSend] starts returning `true`. However, [isClosedForReceive][ReceiveChannel.isClosedForReceive]
     * on the side of [ReceiveChannel] starts returning `true` only after all previously sent elements
     * are received.
     *
     * A channel that was closed without a [cause] throws [ClosedSendChannelException] on attempts to send or receive.
     * A channel that was closed with non-null [cause] is called a _failed_ channel. Attempts to send or
     * receive on a failed channel throw the specified [cause] exception.
     */
    public fun close(cause: Throwable? = null): Boolean
}

/**
 * Receiver's interface to [Channel].
 */
public interface ReceiveChannel<out E> {
    /**
     * Returns `true` if this channel was closed by invocation of [close][SendChannel.close] on the [SendChannel]
     * side and all previously sent items were already received, so that the [receive] attempt
     * throws [ClosedReceiveChannelException]. If the channel was closed because of the exception, it
     * is considered closed, too, but it is called a _failed_ channel. All suspending attempts to receive
     * an element from a failed channel throw the original [close][SendChannel.close] cause exception.
     */
    public val isClosedForReceive: Boolean

    /**
     * Returns `true` if the channel is empty (contains no elements) and the [receive] attempt will suspend.
     * This function returns `false` for [isClosedForReceive] channel.
     */
    public val isEmpty: Boolean

    /**
     * Retrieves and removes the element from this channel suspending the caller while this channel [isEmpty]
     * or throws [ClosedReceiveChannelException] if the channel [isClosedForReceive].
     * If the channel was closed because of the exception, it is called a _failed_ channel and this function
     * throws the original [close][SendChannel.close] cause exception.
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this
     * function is suspended, this function immediately resumes with [CancellationException].
     *
     * *Cancellation of suspended receive is atomic* -- when this function
     * throws [CancellationException] it means that the element was not retrieved from this channel.
     * As a side-effect of atomic cancellation, a thread-bound coroutine (to some UI thread, for example) may
     * continue to execute even after it was cancelled from the same thread in the case when this receive operation
     * was already resumed and the continuation was posted for execution to the thread's queue.
     *
     * Note, that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     *
     * This function can be used in [select] invocation with [onReceive] clause.
     * Use [poll] to try receiving from this channel without waiting.
     */
    public suspend fun receive(): E

    /**
     * Clause for [select] expression of [receive] suspending function that selects with the element that
     * is received from the channel.
     * The [select] invocation fails with exception if the channel
     * [isClosedForReceive] (see [close][SendChannel.close] for details).
     */
    public val onReceive: SelectClause1<E>

    /**
     * Retrieves and removes the element from this channel suspending the caller while this channel [isEmpty]
     * or returns `null` if the channel is [closed][isClosedForReceive] without cause
     * or throws the original [close][SendChannel.close] cause exception if the channel has _failed_.
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this
     * function is suspended, this function immediately resumes with [CancellationException].
     *
     * *Cancellation of suspended receive is atomic* -- when this function
     * throws [CancellationException] it means that the element was not retrieved from this channel.
     * As a side-effect of atomic cancellation, a thread-bound coroutine (to some UI thread, for example) may
     * continue to execute even after it was cancelled from the same thread in the case when this receive operation
     * was already resumed and the continuation was posted for execution to the thread's queue.
     *
     * Note, that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     *
     * This function can be used in [select] invocation with [onReceiveOrNull] clause.
     * Use [poll] to try receiving from this channel without waiting.
     */
    public suspend fun receiveOrNull(): E?

    /**
     * Clause for [select] expression of [receiveOrNull] suspending function that selects with the element that
     * is received from the channel or selects with `null` if if the channel
     * [isClosedForReceive] without cause. The [select] invocation fails with
     * the original [close][SendChannel.close] cause exception if the channel has _failed_.
     */
    public val onReceiveOrNull: SelectClause1<E?>

    /**
     * Retrieves and removes the element from this channel, or returns `null` if this channel [isEmpty]
     * or is [isClosedForReceive] without cause.
     * It throws the original [close][SendChannel.close] cause exception if the channel has _failed_.
     */
    public fun poll(): E?

    /**
     * Returns new iterator to receive elements from this channels using `for` loop.
     * Iteration completes normally when the channel is [isClosedForReceive] without cause and
     * throws the original [close][SendChannel.close] cause exception if the channel has _failed_.
     */
    public operator fun iterator(): ChannelIterator<E>

    /**
     * Cancels reception of remaining elements from this channel. This function closes the channel with
     * the specified cause (unless it was already closed) and removes all buffered sent elements from it.
     * This function returns `true` if the channel was not closed previously, or `false` otherwise.
     *
     * Immediately after invocation of this function [isClosedForReceive] and
     * [isClosedForSend][SendChannel.isClosedForSend]
     * on the side of [SendChannel] start returning `true`, so all attempts to send to this channel
     * afterwards will throw [ClosedSendChannelException], while attempts to receive will throw
     * [ClosedReceiveChannelException] if it was cancelled without a cause.
     * A channel that was cancelled with non-null [cause] is called a _failed_ channel. Attempts to send or
     * receive on a failed channel throw the specified [cause] exception.
     */
    public fun cancel(cause: Throwable? = null): Boolean
}

/**
 * Iterator for [ReceiveChannel]. Instances of this interface are *not thread-safe* and shall not be used
 * from concurrent coroutines.
 */
public interface ChannelIterator<out E> {
    /**
     * Returns `true` if the channel has more elements suspending the caller while this channel
     * [isEmpty][ReceiveChannel.isEmpty] or returns `false` if the channel
     * [isClosedForReceive][ReceiveChannel.isClosedForReceive] without cause.
     * It throws the original [close][SendChannel.close] cause exception if the channel has _failed_.
     *
     * This function retrieves and removes the element from this channel for the subsequent invocation
     * of [next].
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this
     * function is suspended, this function immediately resumes with [CancellationException].
     *
     * *Cancellation of suspended receive is atomic* -- when this function
     * throws [CancellationException] it means that the element was not retrieved from this channel.
     * As a side-effect of atomic cancellation, a thread-bound coroutine (to some UI thread, for example) may
     * continue to execute even after it was cancelled from the same thread in the case when this receive operation
     * was already resumed and the continuation was posted for execution to the thread's queue.
     *
     * Note, that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     */
    public suspend operator fun hasNext(): Boolean

    /**
     * Retrieves and removes the element from this channel suspending the caller while this channel
     * [isEmpty][ReceiveChannel.isEmpty] or throws [ClosedReceiveChannelException] if the channel
     * [isClosedForReceive][ReceiveChannel.isClosedForReceive] without cause.
     * It throws the original [close][SendChannel.close] cause exception if the channel has _failed_.
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this
     * function is suspended, this function immediately resumes with [CancellationException].
     *
     * *Cancellation of suspended receive is atomic* -- when this function
     * throws [CancellationException] it means that the element was not retrieved from this channel.
     * As a side-effect of atomic cancellation, a thread-bound coroutine (to some UI thread, for example) may
     * continue to execute even after it was cancelled from the same thread in the case when this receive operation
     * was already resumed and the continuation was posted for execution to the thread's queue.
     *
     * Note, that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     */
    public suspend operator fun next(): E
}

/**
 * Channel is a non-blocking primitive for communication between sender using [SendChannel] and receiver using [ReceiveChannel].
 * Conceptually, a channel is similar to [BlockingQueue][java.util.concurrent.BlockingQueue],
 * but it has suspending operations instead of blocking ones and it can be closed.
 *
 * See `Channel(capacity)` factory function for the description of available channel implementations.
 */
public interface Channel<E> : SendChannel<E>, ReceiveChannel<E> {
    /**
     * Constants for channel factory function `Channel()`.
     */
    public companion object Factory {
        /**
         * Requests channel with unlimited capacity buffer in `Channel(...)` factory function --
         * the [LinkedListChannel] gets created.
         */
        public const val UNLIMITED = Int.MAX_VALUE

        /**
         * Requests conflated channel in `Channel(...)` factory function --
         * the [ConflatedChannel] gets created.
         */
        public const val CONFLATED = -1

        /**
         * Creates a channel with the specified buffer capacity (or without a buffer by default).
         * @suppress **Deprecated**
         */
        @Deprecated("Replaced with top-level function", level = DeprecationLevel.HIDDEN)
        public operator fun <E> invoke(capacity: Int = 0): Channel<E> = Channel(capacity)
    }
}

/**
 * Creates a channel without a buffer -- [RendezvousChannel].
 */
public fun <E> Channel(): Channel<E> = RendezvousChannel<E>()

/**
 * Creates a channel with the specified buffer capacity (or without a buffer by default).
 *
 * The resulting channel type depends on the specified [capacity] parameter:
 * * when `capacity` is 0 -- creates [RendezvousChannel] without a buffer;
 * * when `capacity` is [Channel.UNLIMITED] -- creates [LinkedListChannel] with buffer of unlimited size;
 * * when `capacity` is [Channel.CONFLATED] -- creates [ConflatedChannel] that conflates back-to-back sends;
 * * when `capacity` is positive, but less than [UNLIMITED] -- creates [ArrayChannel] with a buffer of the specified `capacity`;
 * * otherwise -- throws [IllegalArgumentException].
 */
public fun <E> Channel(capacity: Int): Channel<E> =
    when (capacity) {
        0 -> RendezvousChannel()
        UNLIMITED -> LinkedListChannel()
        CONFLATED -> ConflatedChannel()
        else -> ArrayChannel(capacity)
    }

/**
 * Indicates attempt to [send][SendChannel.send] on [isClosedForSend][SendChannel.isClosedForSend] channel
 * that was closed without a cause. A _failed_ channel rethrows the original [close][SendChannel.close] cause
 * exception on send attempts.
 */
public class ClosedSendChannelException(message: String?) : CancellationException(message)

/**
 * Indicates attempt to [receive][ReceiveChannel.receive] on [isClosedForReceive][ReceiveChannel.isClosedForReceive]
 * channel that was closed without a cause. A _failed_ channel rethrows the original [close][SendChannel.close] cause
 * exception on receive attempts.
 */
public class ClosedReceiveChannelException(message: String?) : NoSuchElementException(message)
