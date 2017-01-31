package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.CancellationException
import kotlinx.coroutines.experimental.CoroutineScope
import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.yield
import java.util.*

/**
 * Sender's interface to [Channel].
 */
public interface SendChannel<in E> {
    /**
     * Returns `true` if this channel was closed by invocation of [close] and thus
     * the [send] attempt will throw [ClosedSendChannelException].
     */
    public val isClosedForSend: Boolean

    /**
     * Returns `true` if the channel is full (out of capacity) and the [send] attempt will suspend.
     * This function returns `false` for [isClosedForSend] channel.
     */
    public val isFull: Boolean

    /**
     * Adds [element] into to this queue, suspending the caller while this queue [isFull],
     * or throws [ClosedSendChannelException] if the channel [isClosedForSend].
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is completed while this
     * function is suspended, this function immediately resumes with [CancellationException].
     * Cancellation of suspended send is *atomic* -- when this function
     * throws [CancellationException] it means that the [element] was not sent to this channel.
     *
     * Note, that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     */
    public suspend fun send(element: E)

    /**
     * Adds [element] into this queue if it is possible to do so immediately without violating capacity restrictions
     * and returns `true`. Otherwise, it returns `false` immediately
     * or throws [ClosedSendChannelException] if the channel [isClosedForSend].
     */
    public fun offer(element: E): Boolean

    /**
     * Closes this channel. This is an idempotent operation -- repeated invocations of this function have no effect.
     * Conceptually, its sends a special close token of this channel. Immediately after invocation of this function
     * [isClosedForSend] starts returning `true`. However, [isClosedForReceive][ReceiveChannel.isClosedForReceive]
     * on the side of [ReceiveChannel] starts returning `true` only after all previously sent elements
     * are received.
     */
    public fun close()
}

/**
 * Receiver's interface to [Channel].
 */
public interface ReceiveChannel<out E> {
    /**
     * Returns `true` if this channel was closed by invocation of [close][SendChannel.close] on the [SendChannel]
     * side and all previously sent items were already received, so that the [receive] attempt will
     * throw [ClosedReceiveChannelException].
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
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is completed while this
     * function is suspended, this function immediately resumes with [CancellationException].
     * Cancellation of suspended receive is *atomic* -- when this function
     * throws [CancellationException] it means that the element was not retrieved from this channel.
     *
     * Note, that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     */
    public suspend fun receive(): E

    /**
     * Retrieves and removes the element from this channel suspending the caller while this channel [isEmpty]
     * or returns `null` if the channel [isClosedForReceive].
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is completed while this
     * function is suspended, this function immediately resumes with [CancellationException].
     * Cancellation of suspended receive is *atomic* -- when this function
     * throws [CancellationException] it means that the element was not retrieved from this channel.
     *
     * Note, that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     */
    public suspend fun receiveOrNull(): E?

    /**
     * Retrieves and removes the head of this queue, or returns `null` if this queue [isEmpty]
     * or [isClosedForReceive].
     */
    public fun pool(): E?

    /**
     * Returns new iterator to receive elements from this channels using `for` loop.
     */
    public operator fun iterator(): ChannelIterator<E>
}

/**
 * Iterator for [ReceiveChannel]. Instances of this interface are *not thread-safe* and shall not be used
 * from concurrent coroutines.
 */
public interface ChannelIterator<out E> {
    /**
     * Returns `true` if the channel has more elements suspending the caller while this channel
     * [isEmpty][ReceiveChannel.isEmpty] or `false` [ClosedReceiveChannelException] if the channel
     * [isClosedForReceive][ReceiveChannel.isClosedForReceive].
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
public interface Channel<E> : SendChannel<E>, ReceiveChannel<E>

/**
 * Indicates attempt to [send][SendChannel.send] on [isClosedForSend][SendChannel.isClosedForSend] channel.
 */
public class ClosedSendChannelException : IllegalStateException()

/**
 * Indicates attempt to [receive][ReceiveChannel.receive] on [isClosedForReceive][ReceiveChannel.isClosedForReceive]
 * channel.
 */
public class ClosedReceiveChannelException : NoSuchElementException()
