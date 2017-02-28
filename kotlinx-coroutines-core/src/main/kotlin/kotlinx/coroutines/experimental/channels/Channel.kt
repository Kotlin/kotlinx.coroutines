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
import kotlinx.coroutines.experimental.selects.SelectBuilder
import kotlinx.coroutines.experimental.selects.SelectInstance
import kotlinx.coroutines.experimental.selects.select
import kotlinx.coroutines.experimental.yield

/**
 * Sender's interface to [Channel].
 */
public interface SendChannel<in E> {
    /**
     * Returns `true` if this channel was closed by invocation of [close] and thus
     * the [send] attempt throws [ClosedSendChannelException]. If the channel was closed because of the exception, it
     * is considered closed, too, but it is called a _failed_ channel. All suspending attempts to send
     * an element to a failed channel throw the original [close] cause exception.
     */
    public val isClosedForSend: Boolean

    /**
     * Returns `true` if the channel is full (out of capacity) and the [send] attempt will suspend.
     * This function returns `false` for [isClosedForSend] channel.
     */
    public val isFull: Boolean

    /**
     * Adds [element] into to this channel, suspending the caller while this channel [isFull],
     * or throws [ClosedSendChannelException] if the channel [isClosedForSend] _normally_.
     * It throws the original [close] cause exception if the channel has _failed_.
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is completed while this
     * function is suspended, this function immediately resumes with [CancellationException].
     * Cancellation of suspended send is *atomic* -- when this function
     * throws [CancellationException] it means that the [element] was not sent to this channel.
     *
     * Note, that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     *
     * This function can be used in [select] invocation with [onSend][SelectBuilder.onSend] clause.
     * Use [offer] to try sending to this channel without waiting.
     */
    public suspend fun send(element: E)

    /**
     * Adds [element] into this queue if it is possible to do so immediately without violating capacity restrictions
     * and returns `true`. Otherwise, it returns `false` immediately
     * or throws [ClosedSendChannelException] if the channel [isClosedForSend] _normally_.
     * It throws the original [close] cause exception if the channel has _failed_.
     */
    public fun offer(element: E): Boolean

    /**
     * Registers [onSend][SelectBuilder.onSend] select clause.
     * @suppress **This is unstable API and it is subject to change.**
     */
    public fun <R> registerSelectSend(select: SelectInstance<R>, element: E, block: suspend () -> R)

    /**
     * Closes this channel with an optional exceptional [cause].
     * This is an idempotent operation -- repeated invocations of this function have no effect and return `false`.
     * Conceptually, its sends a special close token of this channel. Immediately after invocation of this function
     * [isClosedForSend] starts returning `true`. However, [isClosedForReceive][ReceiveChannel.isClosedForReceive]
     * on the side of [ReceiveChannel] starts returning `true` only after all previously sent elements
     * are received.
     *
     * A channel that was closed without a [cause], is considered to be _closed normally_.
     * A channel that was closed with non-null [cause] is called a _failed channel_. Attempts to send or
     * receive on a failed channel throw this cause exception.
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
     * This suspending function is cancellable. If the [Job] of the current coroutine is completed while this
     * function is suspended, this function immediately resumes with [CancellationException].
     * Cancellation of suspended receive is *atomic* -- when this function
     * throws [CancellationException] it means that the element was not retrieved from this channel.
     *
     * Note, that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     *
     * This function can be used in [select] invocation with [onReceive][SelectBuilder.onReceive] clause.
     * Use [poll] to try receiving from this channel without waiting.
     */
    public suspend fun receive(): E

    /**
     * Retrieves and removes the element from this channel suspending the caller while this channel [isEmpty]
     * or returns `null` if the channel is [closed][isClosedForReceive] _normally_,
     * or throws the original [close][SendChannel.close] cause exception if the channel has _failed_.
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is completed while this
     * function is suspended, this function immediately resumes with [CancellationException].
     * Cancellation of suspended receive is *atomic* -- when this function
     * throws [CancellationException] it means that the element was not retrieved from this channel.
     *
     * Note, that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     *
     * This function can be used in [select] invocation with [onReceiveOrNull][SelectBuilder.onReceiveOrNull] clause.
     * Use [poll] to try receiving from this channel without waiting.
     */
    public suspend fun receiveOrNull(): E?

    /**
     * Retrieves and removes the head of this queue, or returns `null` if this queue [isEmpty]
     * or is [closed][isClosedForReceive] _normally_,
     * or throws the original [close][SendChannel.close] cause exception if the channel has _failed_.
     */
    public fun poll(): E?

    /**
     * Returns new iterator to receive elements from this channels using `for` loop.
     * Iteration completes normally when the channel is [closed][isClosedForReceive] _normally_ and
     * throws the original [close][SendChannel.close] cause exception if the channel has _failed_.
     */
    public operator fun iterator(): ChannelIterator<E>

    /**
     * Registers [onReceive][SelectBuilder.onReceive] select clause.
     * @suppress **This is unstable API and it is subject to change.**
     */
    public fun <R> registerSelectReceive(select: SelectInstance<R>, block: suspend (E) -> R)

    /**
     * Registers [onReceiveOrNull][SelectBuilder.onReceiveOrNull] select clause.
     * @suppress **This is unstable API and it is subject to change.**
     */
    public fun <R> registerSelectReceiveOrNull(select: SelectInstance<R>, block: suspend (E?) -> R)
}

/**
 * Iterator for [ReceiveChannel]. Instances of this interface are *not thread-safe* and shall not be used
 * from concurrent coroutines.
 */
public interface ChannelIterator<out E> {
    /**
     * Returns `true` if the channel has more elements suspending the caller while this channel
     * [isEmpty][ReceiveChannel.isEmpty] or returns `false` if the channel
     * [isClosedForReceive][ReceiveChannel.isClosedForReceive] _normally_.
     * It throws the original [close][SendChannel.close] cause exception if the channel has _failed_.
     *
     * This function retrieves and removes the element from this channel for the subsequent invocation
     * of [next].
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is completed while this
     * function is suspended, this function immediately resumes with [CancellationException].
     * Cancellation of suspended receive is *atomic* -- when this function
     * throws [CancellationException] it means that the element was not retrieved from this channel.
     *
     * Note, that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     */
    public suspend operator fun hasNext(): Boolean

    /**
     * Retrieves and removes the element from this channel suspending the caller while this channel
     * [isEmpty][ReceiveChannel.isEmpty] or throws [ClosedReceiveChannelException] if the channel
     * [isClosedForReceive][ReceiveChannel.isClosedForReceive].
     * It throws the original [close][SendChannel.close] cause exception if the channel has _failed_.
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is completed while this
     * function is suspended, this function immediately resumes with [CancellationException].
     * Cancellation of suspended receive is *atomic* -- when this function
     * throws [CancellationException] it means that the element was not retrieved from this channel.
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
 */
public interface Channel<E> : SendChannel<E>, ReceiveChannel<E> {
    /**
     * Factory for channels.
     */
    public companion object Factory {
        /**
         * Requests channel with unlimited capacity buffer in [Channel()][invoke] factory function.
         */
        public const val UNLIMITED = Int.MAX_VALUE

        /**
         * Creates a channel with specified buffer capacity (or without a buffer by default).
         *
         * The resulting channel type depends on the specified [capacity] parameter:
         * * when `capacity` is 0 -- creates [RendezvousChannel];
         * * when `capacity` is [UNLIMITED] -- creates [LinkedListChannel];
         * * otherwise -- creates [ArrayChannel].
         */
        public operator fun <E> invoke(capacity: Int = 0): Channel<E> {
            check(capacity >= 0) { "Channel capacity cannot be negative, but $capacity was specified" }
            return when (capacity) {
                0 -> RendezvousChannel()
                UNLIMITED -> LinkedListChannel()
                else -> ArrayChannel(capacity)
            }
        }
    }
}

/**
 * Indicates attempt to [send][SendChannel.send] on [isClosedForSend][SendChannel.isClosedForSend] channel
 * that was closed _normally_. A _failed_ channel rethrows the original [close][SendChannel.close] cause
 * exception on send attempts.
 */
public class ClosedSendChannelException(message: String?) : CancellationException(message)

/**
 * Indicates attempt to [receive][ReceiveChannel.receive] on [isClosedForReceive][ReceiveChannel.isClosedForReceive]
 * channel that was closed _normally_. A _failed_ channel rethrows the original [close][SendChannel.close] cause
 * exception on receive attempts.
 */
public class ClosedReceiveChannelException(message: String?) : NoSuchElementException(message)
