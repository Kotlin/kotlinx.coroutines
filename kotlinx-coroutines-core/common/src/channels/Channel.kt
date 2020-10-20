/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("FunctionName")

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.Channel.Factory.BUFFERED
import kotlinx.coroutines.channels.Channel.Factory.CHANNEL_DEFAULT_CAPACITY
import kotlinx.coroutines.channels.Channel.Factory.CONFLATED
import kotlinx.coroutines.channels.Channel.Factory.RENDEZVOUS
import kotlinx.coroutines.channels.Channel.Factory.UNLIMITED
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*
import kotlin.internal.*
import kotlin.jvm.*

/**
 * Sender's interface to [Channel].
 */
public interface SendChannel<in E> {
    /**
     * Returns `true` if this channel was closed by an invocation of [close]. This means that
     * calling [send] or [offer] will result in an exception.
     *
     * **Note: This is an experimental api.** This property may change its semantics and/or name in the future.
     */
    @ExperimentalCoroutinesApi
    public val isClosedForSend: Boolean

    /**
     * Returns `true` if the channel is full (out of capacity), which means that an attempt to [send] will suspend.
     * This function returns `false`  if the channel [is closed for `send`][isClosedForSend].
     *
     * @suppress **Will be removed in next releases, no replacement.**
     */
    @ExperimentalCoroutinesApi
    @Deprecated(level = DeprecationLevel.ERROR, message = "Will be removed in next releases without replacement")
    public val isFull: Boolean

    /**
     * Sends the specified [element] to this channel, suspending the caller while the buffer of this channel is full
     * or if it does not exist, or throws an exception if the channel [is closed for `send`][isClosedForSend] (see [close] for details).
     *
     * [Closing][close] a channel _after_ this function has suspended does not cause this suspended [send] invocation
     * to abort, because closing a channel is conceptually like sending a special "close token" over this channel.
     * All elements sent over the channel are delivered in first-in first-out order. The sent element
     * will be delivered to receivers before the close token.
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this
     * function is suspended, this function immediately resumes with a [CancellationException].
     * There is a **prompt cancellation guarantee**. If the job was cancelled while this function was
     * suspended, it will not resume successfully. The `send` call can send the element to the channel,
     * but then throw [CancellationException], thus an exception should not be treated as a failure to deliver the element.
     * See "Undelivered elements" section in [Channel] documentation for details on handling undelivered elements.
     *
     * Note that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     *
     * This function can be used in [select] invocations with the [onSend] clause.
     * Use [offer] to try sending to this channel without waiting.
     */
    public suspend fun send(element: E)

    /**
     * Clause for the [select] expression of the [send] suspending function that selects when the element that is specified
     * as the parameter is sent to the channel. When the clause is selected, the reference to this channel
     * is passed into the corresponding block.
     *
     * The [select] invocation fails with an exception if the channel [is closed for `send`][isClosedForSend] (see [close] for details).
     */
    public val onSend: SelectClause2<E, SendChannel<E>>

    /**
     * Immediately adds the specified [element] to this channel, if this doesn't violate its capacity restrictions,
     * and returns `true`. Otherwise, just returns `false`. This is a synchronous variant of [send] which backs off
     * in situations when `send` suspends.
     *
     * Throws an exception if the channel [is closed for `send`][isClosedForSend] (see [close] for details).
     *
     * When `offer` call returns `false` it guarantees that the element was not delivered to the consumer and it
     * it does not call `onUndeliveredElement` that was installed for this channel. If the channel was closed,
     * then it calls `onUndeliveredElement` before throwing an exception.
     * See "Undelivered elements" section in [Channel] documentation for details on handling undelivered elements.
     */
    public fun offer(element: E): Boolean

    /**
     * Closes this channel.
     * This is an idempotent operation &mdash; subsequent invocations of this function have no effect and return `false`.
     * Conceptually, its sends a special "close token" over this channel.
     *
     * Immediately after invocation of this function,
     * [isClosedForSend] starts returning `true`. However, [isClosedForReceive][ReceiveChannel.isClosedForReceive]
     * on the side of [ReceiveChannel] starts returning `true` only after all previously sent elements
     * are received.
     *
     * A channel that was closed without a [cause] throws a [ClosedSendChannelException] on attempts to [send] or [offer]
     * and [ClosedReceiveChannelException] on attempts to [receive][ReceiveChannel.receive].
     * A channel that was closed with non-null [cause] is called a _failed_ channel. Attempts to send or
     * receive on a failed channel throw the specified [cause] exception.
     */
    public fun close(cause: Throwable? = null): Boolean

    /**
     * Registers a [handler] which is synchronously invoked once the channel is [closed][close]
     * or the receiving side of this channel is [cancelled][ReceiveChannel.cancel].
     * Only one handler can be attached to a channel during its lifetime.
     * The `handler` is invoked when [isClosedForSend] starts to return `true`.
     * If the channel is closed already, the handler is invoked immediately.
     *
     * The meaning of `cause` that is passed to the handler:
     * * `null` if the channel was closed or cancelled without the corresponding argument
     * * the cause of `close` or `cancel` otherwise.
     *
     * Example of usage (exception handling is omitted):
     * ```
     * val events = Channel(UNLIMITED)
     * callbackBasedApi.registerCallback { event ->
     *   events.offer(event)
     * }
     *
     * val uiUpdater = launch(Dispatchers.Main, parent = UILifecycle) {
     *    events.consume {}
     *    events.cancel()
     * }
     *
     * events.invokeOnClose { callbackBasedApi.stop() }
     *
     * ```
     *
     * **Note: This is an experimental api.** This function may change its semantics, parameters or return type in the future.
     *
     * @throws UnsupportedOperationException if the underlying channel doesn't support [invokeOnClose].
     * Implementation note: currently, [invokeOnClose] is unsupported only by Rx-like integrations
     *
     * @throws IllegalStateException if another handler was already registered
     */
    @ExperimentalCoroutinesApi
    public fun invokeOnClose(handler: (cause: Throwable?) -> Unit)
}

/**
 * Receiver's interface to [Channel].
 */
public interface ReceiveChannel<out E> {
    /**
     * Returns `true` if this channel was closed by invocation of [close][SendChannel.close] on the [SendChannel]
     * side and all previously sent items were already received. This means that calling [receive]
     * will result in a [ClosedReceiveChannelException]. If the channel was closed because of an exception, it
     * is considered closed, too, but is called a _failed_ channel. All suspending attempts to receive
     * an element from a failed channel throw the original [close][SendChannel.close] cause exception.
     *
     * **Note: This is an experimental api.** This property may change its semantics and/or name in the future.
     */
    @ExperimentalCoroutinesApi
    public val isClosedForReceive: Boolean

    /**
     * Returns `true` if the channel is empty (contains no elements), which means that an attempt to [receive] will suspend.
     * This function returns `false` if the channel [is closed for `receive`][isClosedForReceive].
     */
    @ExperimentalCoroutinesApi
    public val isEmpty: Boolean

    /**
     * Retrieves and removes an element from this channel if it's not empty, or suspends the caller while the channel is empty,
     * or throws a [ClosedReceiveChannelException] if the channel [is closed for `receive`][isClosedForReceive].
     * If the channel was closed because of an exception, it is called a _failed_ channel and this function
     * will throw the original [close][SendChannel.close] cause exception.
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this
     * function is suspended, this function immediately resumes with a [CancellationException].
     * There is a **prompt cancellation guarantee**. If the job was cancelled while this function was
     * suspended, it will not resume successfully. The `receive` call can retrieve the element from the channel,
     * but then throw [CancellationException], thus failing to deliver the element.
     * See "Undelivered elements" section in [Channel] documentation for details on handling undelivered elements.
     *
     * Note that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     *
     * This function can be used in [select] invocations with the [onReceive] clause.
     * Use [poll] to try receiving from this channel without waiting.
     */
    public suspend fun receive(): E

    /**
     * Clause for the [select] expression of the [receive] suspending function that selects with the element
     * received from the channel.
     * The [select] invocation fails with an exception if the channel
     * [is closed for `receive`][isClosedForReceive] (see [close][SendChannel.close] for details).
     */
    public val onReceive: SelectClause1<E>

    /**
     * Retrieves and removes an element from this channel if it's not empty, or suspends the caller while the channel is empty,
     * or returns `null` if the channel is [closed for `receive`][isClosedForReceive] without cause,
     * or throws the original [close][SendChannel.close] cause exception if the channel has _failed_.
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this
     * function is suspended, this function immediately resumes with a [CancellationException].
     * There is a **prompt cancellation guarantee**. If the job was cancelled while this function was
     * suspended, it will not resume successfully.  The `receiveOrNull` call can retrieve the element from the channel,
     * but then throw [CancellationException], thus failing to deliver the element.
     * See "Undelivered elements" section in [Channel] documentation for details on handling undelivered elements.
     *
     * Note that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     *
     * This function can be used in [select] invocations with the [onReceiveOrNull] clause.
     * Use [poll] to try receiving from this channel without waiting.
     *
     * @suppress **Deprecated**: in favor of receiveOrClosed and receiveOrNull extension.
     */
    @ObsoleteCoroutinesApi
    @Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")
    @LowPriorityInOverloadResolution
    @Deprecated(
        message = "Deprecated in favor of receiveOrClosed and receiveOrNull extension",
        level = DeprecationLevel.WARNING,
        replaceWith = ReplaceWith("receiveOrNull", "kotlinx.coroutines.channels.receiveOrNull")
    )
    public suspend fun receiveOrNull(): E?

    /**
     * Clause for the [select] expression of the [receiveOrNull] suspending function that selects with the element
     * received from the channel or `null` if the channel is
     * [closed for `receive`][isClosedForReceive] without a cause. The [select] invocation fails with
     * the original [close][SendChannel.close] cause exception if the channel has _failed_.
     *
     * @suppress **Deprecated**: in favor of onReceiveOrClosed and onReceiveOrNull extension.
     */
    @ObsoleteCoroutinesApi
    @Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")
    @LowPriorityInOverloadResolution
    @Deprecated(
        message = "Deprecated in favor of onReceiveOrClosed and onReceiveOrNull extension",
        level = DeprecationLevel.WARNING,
        replaceWith = ReplaceWith("onReceiveOrNull", "kotlinx.coroutines.channels.onReceiveOrNull")
    )
    public val onReceiveOrNull: SelectClause1<E?>

    /**
     * Retrieves and removes an element from this channel if it's not empty, or suspends the caller while this channel is empty.
     * This method returns [ValueOrClosed] with the value of an element successfully retrieved from the channel
     * or the close cause if the channel was closed.
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this
     * function is suspended, this function immediately resumes with a [CancellationException].
     * There is a **prompt cancellation guarantee**. If the job was cancelled while this function was
     * suspended, it will not resume successfully. The `receiveOrClosed` call can retrieve the element from the channel,
     * but then throw [CancellationException], thus failing to deliver the element.
     * See "Undelivered elements" section in [Channel] documentation for details on handling undelivered elements.
     *
     * Note that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     *
     * This function can be used in [select] invocations with the [onReceiveOrClosed] clause.
     * Use [poll] to try receiving from this channel without waiting.
     *
     * @suppress *This is an internal API, do not use*: Inline classes ABI is not stable yet and
     *            [KT-27524](https://youtrack.jetbrains.com/issue/KT-27524) needs to be fixed.
     */
    @InternalCoroutinesApi // until https://youtrack.jetbrains.com/issue/KT-27524 is fixed
    public suspend fun receiveOrClosed(): ValueOrClosed<E>

    /**
     * Clause for the [select] expression of the [receiveOrClosed] suspending function that selects with the [ValueOrClosed] with a value
     * that is received from the channel or with a close cause if the channel
     * [is closed for `receive`][isClosedForReceive].
     *
     * @suppress *This is an internal API, do not use*: Inline classes ABI is not stable yet and
     *            [KT-27524](https://youtrack.jetbrains.com/issue/KT-27524) needs to be fixed.
     */
    @InternalCoroutinesApi // until https://youtrack.jetbrains.com/issue/KT-27524 is fixed
    public val onReceiveOrClosed: SelectClause1<ValueOrClosed<E>>

    /**
     * Retrieves and removes an element from this channel if its not empty, or returns `null` if the channel is empty
     * or is [is closed for `receive`][isClosedForReceive] without a cause.
     * It throws the original [close][SendChannel.close] cause exception if the channel has _failed_.
     */
    public fun poll(): E?

    /**
     * Returns a new iterator to receive elements from this channel using a `for` loop.
     * Iteration completes normally when the channel [is closed for `receive`][isClosedForReceive] without a cause and
     * throws the original [close][SendChannel.close] cause exception if the channel has _failed_.
     */
    public operator fun iterator(): ChannelIterator<E>

    /**
     * Cancels reception of remaining elements from this channel with an optional [cause].
     * This function closes the channel and removes all buffered sent elements from it.
     *
     * A cause can be used to specify an error message or to provide other details on
     * the cancellation reason for debugging purposes.
     * If the cause is not specified, then an instance of [CancellationException] with a
     * default message is created to [close][SendChannel.close] the channel.
     *
     * Immediately after invocation of this function [isClosedForReceive] and
     * [isClosedForSend][SendChannel.isClosedForSend]
     * on the side of [SendChannel] start returning `true`. Any attempt to send to or receive from this channel
     * will lead to a [CancellationException].
     */
    public fun cancel(cause: CancellationException? = null)

    /**
     * @suppress This method implements old version of JVM ABI. Use [cancel].
     */
    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.2.0, binary compatibility with versions <= 1.1.x")
    public fun cancel(): Unit = cancel(null)

    /**
     * @suppress This method has bad semantics when cause is not a [CancellationException]. Use [cancel].
     */
    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.2.0, binary compatibility with versions <= 1.1.x")
    public fun cancel(cause: Throwable? = null): Boolean
}

/**
 * A discriminated union of [ReceiveChannel.receiveOrClosed] result
 * that encapsulates either an element of type [T] successfully received from the channel or a close cause.
 *
 * :todo: Do not make it public before resolving todos in the code of this class.
 *
 * @suppress *This is an internal API, do not use*: Inline classes ABI is not stable yet and
 *            [KT-27524](https://youtrack.jetbrains.com/issue/KT-27524) needs to be fixed.
 */
@Suppress("NON_PUBLIC_PRIMARY_CONSTRUCTOR_OF_INLINE_CLASS", "EXPERIMENTAL_FEATURE_WARNING")
@InternalCoroutinesApi // until https://youtrack.jetbrains.com/issue/KT-27524 is fixed
public inline class ValueOrClosed<out T>
internal constructor(private val holder: Any?) {
    /**
     * Returns `true` if this instance represents a received element.
     * In this case [isClosed] returns `false`.
     * todo: it is commented for now, because it is not used
     */
    //public val isValue: Boolean get() = holder !is Closed

    /**
     * Returns `true` if this instance represents a close cause.
     * In this case [isValue] returns `false`.
     */
    public val isClosed: Boolean get() = holder is Closed

    /**
     * Returns the received value if this instance represents a received value, or throws an [IllegalStateException] otherwise.
     *
     * :todo: Decide, if it is needed, how it shall be named with relation to [valueOrThrow]:
     *
     * So we have the following methods on `ValueOrClosed`: `value`, `valueOrNull`, `valueOrThrow`.
     * On the other hand, the channel has the following `receive` variants:
     *  * `receive` which corresponds to `receiveOrClosed().valueOrThrow`... huh?
     *  * `receiveOrNull` which corresponds to `receiveOrClosed().valueOrNull`
     *  * `receiveOrClosed`
     * For the sake of simplicity consider dropping this version of `value` and rename [valueOrThrow] to simply `value`.
     */
    @Suppress("UNCHECKED_CAST")
    public val value: T
        get() = if (holder is Closed) error(DEFAULT_CLOSE_MESSAGE) else holder as T

    /**
     * Returns the received value if this element represents a received value, or `null` otherwise.
     * :todo: Decide if it shall be made into extension that is available only for non-null T.
     * Note: it might become inconsistent with kotlin.Result
     */
    @Suppress("UNCHECKED_CAST")
    public val valueOrNull: T?
        get() = if (holder is Closed) null else holder as T

    /**
     * :todo: Decide, if it is needed, how it shall be named with relation to [value].
     * Note that `valueOrThrow` rethrows the cause adding no meaningful information about the call site,
     * so if one is sure that `ValueOrClosed` always holds a value, this very property should be used.
     * Otherwise, it could be very hard to locate the source of the exception.
     * todo: it is commented for now, because it is not used
     */
    //@Suppress("UNCHECKED_CAST")
    //public val valueOrThrow: T
    //    get() = if (holder is Closed) throw holder.exception else holder as T

    /**
     * Returns the close cause of the channel if this instance represents a close cause, or throws
     * an [IllegalStateException] otherwise.
     */
    @Suppress("UNCHECKED_CAST")
    public val closeCause: Throwable? get() =
        if (holder is Closed) holder.cause else error("Channel was not closed")

    /**
     * @suppress
     */
    public override fun toString(): String =
        when (holder) {
            is Closed -> holder.toString()
            else -> "Value($holder)"
    }

    internal class Closed(@JvmField val cause: Throwable?) {
        // todo: it is commented for now, because it is not used
        //val exception: Throwable get() = cause ?: ClosedReceiveChannelException(DEFAULT_CLOSE_MESSAGE)
        override fun equals(other: Any?): Boolean = other is Closed && cause == other.cause
        override fun hashCode(): Int = cause.hashCode()
        override fun toString(): String = "Closed($cause)"
    }

    /**
     * todo: consider making value/closed constructors public in the future.
     */
    internal companion object {
        @Suppress("NOTHING_TO_INLINE")
        internal inline fun <E> value(value: E): ValueOrClosed<E> =
            ValueOrClosed(value)

        @Suppress("NOTHING_TO_INLINE")
        internal inline fun <E> closed(cause: Throwable?): ValueOrClosed<E> =
            ValueOrClosed(Closed(cause))
    }
}

/**
 * Iterator for [ReceiveChannel]. Instances of this interface are *not thread-safe* and shall not be used
 * from concurrent coroutines.
 */
public interface ChannelIterator<out E> {
    /**
     * Returns `true` if the channel has more elements, suspending the caller while this channel is empty,
     * or returns `false` if the channel [is closed for `receive`][ReceiveChannel.isClosedForReceive] without a cause.
     * It throws the original [close][SendChannel.close] cause exception if the channel has _failed_.
     *
     * This function retrieves and removes an element from this channel for the subsequent invocation
     * of [next].
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this
     * function is suspended, this function immediately resumes with a [CancellationException].
     * There is a **prompt cancellation guarantee**. If the job was cancelled while this function was
     * suspended, it will not resume successfully. The `hasNext` call can retrieve the element from the channel,
     * but then throw [CancellationException], thus failing to deliver the element.
     * See "Undelivered elements" section in [Channel] documentation for details on handling undelivered elements.
     *
     * Note that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     */
    public suspend operator fun hasNext(): Boolean

    @Deprecated(message = "Since 1.3.0, binary compatibility with versions <= 1.2.x", level = DeprecationLevel.HIDDEN)
    @Suppress("INAPPLICABLE_JVM_NAME")
    @JvmName("next")
    public suspend fun next0(): E {
        /*
         * Before 1.3.0 the "next()" could have been used without invoking "hasNext" first and there were code samples
         * demonstrating this behavior, so we preserve this logic for full binary backwards compatibility with previously
         * compiled code.
         */
        if (!hasNext()) throw ClosedReceiveChannelException(DEFAULT_CLOSE_MESSAGE)
        return next()
    }

    /**
     * Retrieves the element removed from the channel by a preceding call to [hasNext], or
     * throws an [IllegalStateException] if [hasNext] was not invoked.
     * This method should only be used in pair with [hasNext]:
     * ```
     * while (iterator.hasNext()) {
     *     val element = iterator.next()
     *     // ... handle element ...
     * }
     * ```
     *
     * This method throws a [ClosedReceiveChannelException] if the channel [is closed for `receive`][ReceiveChannel.isClosedForReceive] without a cause.
     * It throws the original [close][SendChannel.close] cause exception if the channel has _failed_.
     */
    public operator fun next(): E
}

/**
 * Channel is a non-blocking primitive for communication between a sender (via [SendChannel]) and a receiver (via [ReceiveChannel]).
 * Conceptually, a channel is similar to Java's [BlockingQueue][java.util.concurrent.BlockingQueue],
 * but it has suspending operations instead of blocking ones and can be [closed][SendChannel.close].
 *
 * ### Creating channels
 *
 * The `Channel(capacity)` factory function is used to create channels of different kinds depending on
 * the value of the `capacity` integer:
 *
 * * When `capacity` is 0 &mdash; it creates a _rendezvous_ channel.
 *   This channel does not have any buffer at all. An element is transferred from the sender
 *   to the receiver only when [send] and [receive] invocations meet in time (rendezvous), so [send] suspends
 *   until another coroutine invokes [receive], and [receive] suspends until another coroutine invokes [send].
 *
 * * When `capacity` is [Channel.UNLIMITED] &mdash; it creates a channel with effectively unlimited buffer.
 *   This channel has a linked-list buffer of unlimited capacity (limited only by available memory).
 *   [Sending][send] to this channel never suspends, and [offer] always returns `true`.
 *
 * * When `capacity` is [Channel.CONFLATED] &mdash; it creates a _conflated_ channel
 *   This channel buffers at most one element and conflates all subsequent `send` and `offer` invocations,
 *   so that the receiver always gets the last element sent.
 *   Back-to-send sent elements are conflated &mdash; only the last sent element is received,
 *   while previously sent elements **are lost**.
 *   [Sending][send] to this channel never suspends, and [offer] always returns `true`.
 *
 * * When `capacity` is positive but less than [UNLIMITED] &mdash; it creates an array-based channel with the specified capacity.
 *   This channel has an array buffer of a fixed `capacity`.
 *   [Sending][send] suspends only when the buffer is full, and [receiving][receive] suspends only when the buffer is empty.
 *
 * Buffered channels can be configured with an additional [`onBufferOverflow`][BufferOverflow] parameter. It controls the behaviour
 * of the channel's [send][Channel.send] function on buffer overflow:
 *
 * * [SUSPEND][BufferOverflow.SUSPEND] &mdash; the default, suspend `send` on buffer overflow until there is
 *   free space in the buffer.
 * * [DROP_OLDEST][BufferOverflow.DROP_OLDEST] &mdash; do not suspend the `send`, add the latest value to the buffer,
 *   drop the oldest one from the buffer.
 *   A channel with `capacity = 1` and `onBufferOverflow = DROP_OLDEST` is a _conflated_ channel.
 * * [DROP_LATEST][BufferOverflow.DROP_LATEST] &mdash; do not suspend the `send`, drop the value that is being sent,
 *   keep the buffer contents intact.
 *
 * A non-default `onBufferOverflow` implicitly creates a channel with at least one buffered element and
 * is ignored for a channel with unlimited buffer. It cannot be specified for `capacity = CONFLATED`, which
 * is a shortcut by itself.
 *
 * ### Prompt cancellation guarantee
 *
 * All suspending functions with channels provide **prompt cancellation guarantee**.
 * If the job was cancelled while send or receive function was suspended, it will not resume successfully,
 * but throws a [CancellationException].
 * With a single-threaded [dispatcher][CoroutineDispatcher] like [Dispatchers.Main] this gives a
 * guarantee that if a piece code running in this thread cancels a [Job], then a coroutine running this job cannot
 * resume successfully and continue to run, ensuring a prompt response to its cancellation.
 *
 * > **Prompt cancellation guarantee** for channel operations was added since `kotlinx.coroutines` version `1.4.0`
 * > and had replaced a channel-specific atomic-cancellation that was not consistent with other suspending functions.
 * > The low-level mechanics of prompt cancellation are explained in [suspendCancellableCoroutine] function.
 *
 * ### Undelivered elements
 *
 * As a result of a prompt cancellation guarantee, when a closeable resource
 * (like open file or a handle to another native resource) is transferred via channel from one coroutine to another
 * it can fail to be delivered and will be lost if either send or receive operations are cancelled in transit.
 *
 * A `Channel()` constructor function has an `onUndeliveredElement` optional parameter.
 * When `onUndeliveredElement` parameter is set, the corresponding function is called once for each element
 * that was sent to the channel with the call to the [send][SendChannel.send] function but failed to be delivered,
 * which can happen in the following cases:
 *
 * * When [send][SendChannel.send] operation throws an exception because it was cancelled before it had a chance to actually
 *   send the element or because the channel was [closed][SendChannel.close] or [cancelled][ReceiveChannel.cancel].
 * * When [offer][SendChannel.offer] operation throws an exception when
 *   the channel was [closed][SendChannel.close] or [cancelled][ReceiveChannel.cancel].
 * * When [receive][ReceiveChannel.receive], [receiveOrNull][ReceiveChannel.receiveOrNull], or [hasNext][ChannelIterator.hasNext]
 *   operation throws an exception when it had retrieved the element from the
 *   channel but was cancelled before the code following the receive call resumed.
 * * The channel was [cancelled][ReceiveChannel.cancel], in which case `onUndeliveredElement` is called on every
 *   remaining element in the channel's buffer.
 *
 * Note, that `onUndeliveredElement` function is called synchronously in an arbitrary context. It should be fast, non-blocking,
 * and should not throw exceptions. Any exception thrown by `onUndeliveredElement` is wrapped into an internal runtime
 * exception which is either rethrown from the caller method or handed off to the exception handler in the current context
 * (see [CoroutineExceptionHandler]) when one is available.
 *
 * A typical usage for `onDeliveredElement` is to close a resource that is being transferred via the channel. The
 * following code pattern guarantees that opened resources are closed even if producer, consumer, and/or channel
 * are cancelled. Resources are never lost.
 *
 * ```
 * // Create the channel with onUndeliveredElement block that closes a resource
 * val channel = Channel<Resource>(capacity) { resource -> resource.close() }
 *
 * // Producer code
 * val resourceToSend = openResource()
 * channel.send(resourceToSend)
 *
 * // Consumer code
 * val resourceReceived = channel.receive()
 * try {
 *     // work with received resource
 * } finally {
 *     resourceReceived.close()
 * }
 * ```
 *
 * > Note, that if you do any kind of work in between `openResource()` and `channel.send(...)`, then you should
 * > ensure that resource gets closed in case this additional code fails.
 */
public interface Channel<E> : SendChannel<E>, ReceiveChannel<E> {
    /**
     * Constants for the channel factory function `Channel()`.
     */
    public companion object Factory {
        /**
         * Requests a channel with an unlimited capacity buffer in the `Channel(...)` factory function.
         */
        public const val UNLIMITED: Int = Int.MAX_VALUE

        /**
         * Requests a rendezvous channel in the `Channel(...)` factory function &mdash; a channel that does not have a buffer.
         */
        public const val RENDEZVOUS: Int = 0

        /**
         * Requests a conflated channel in the `Channel(...)` factory function. This is a shortcut to creating
         * a channel with [`onBufferOverflow = DROP_OLDEST`][BufferOverflow.DROP_OLDEST].
         */
        public const val CONFLATED: Int = -1

        /**
         * Requests a buffered channel with the default buffer capacity in the `Channel(...)` factory function.
         * The default capacity for a channel that [suspends][BufferOverflow.SUSPEND] on overflow
         * is 64 and can be overridden by setting [DEFAULT_BUFFER_PROPERTY_NAME] on JVM.
         * For non-suspending channels, a buffer of capacity 1 is used.
         */
        public const val BUFFERED: Int = -2

        // only for internal use, cannot be used with Channel(...)
        internal const val OPTIONAL_CHANNEL = -3

        /**
         * Name of the property that defines the default channel capacity when
         * [BUFFERED] is used as parameter in `Channel(...)` factory function.
         */
        public const val DEFAULT_BUFFER_PROPERTY_NAME: String = "kotlinx.coroutines.channels.defaultBuffer"

        internal val CHANNEL_DEFAULT_CAPACITY = systemProp(DEFAULT_BUFFER_PROPERTY_NAME,
            64, 1, UNLIMITED - 1
        )
    }
}

/**
 * Creates a channel with the specified buffer capacity (or without a buffer by default).
 * See [Channel] interface documentation for details.
 *
 * @param capacity either a positive channel capacity or one of the constants defined in [Channel.Factory].
 * @param onBufferOverflow configures an action on buffer overflow (optional, defaults to
 *   a [suspending][BufferOverflow.SUSPEND] attempt to [send][Channel.send] a value,
 *   supported only when `capacity >= 0` or `capacity == Channel.BUFFERED`,
 *   implicitly creates a channel with at least one buffered element).
 * @param onUndeliveredElement an optional function that is called when element was sent but was not delivered to the consumer.
 *   See "Undelivered elements" section in [Channel] documentation.
 * @throws IllegalArgumentException when [capacity] < -2
 */
public fun <E> Channel(
    capacity: Int = RENDEZVOUS,
    onBufferOverflow: BufferOverflow = BufferOverflow.SUSPEND,
    onUndeliveredElement: ((E) -> Unit)? = null
): Channel<E> =
    when (capacity) {
        RENDEZVOUS -> {
            if (onBufferOverflow == BufferOverflow.SUSPEND)
                RendezvousChannel(onUndeliveredElement) // an efficient implementation of rendezvous channel
            else
                ArrayChannel(1, onBufferOverflow, onUndeliveredElement) // support buffer overflow with buffered channel
        }
        CONFLATED -> {
            require(onBufferOverflow == BufferOverflow.SUSPEND) {
                "CONFLATED capacity cannot be used with non-default onBufferOverflow"
            }
            ConflatedChannel(onUndeliveredElement)
        }
        UNLIMITED -> LinkedListChannel(onUndeliveredElement) // ignores onBufferOverflow: it has buffer, but it never overflows
        BUFFERED -> ArrayChannel( // uses default capacity with SUSPEND
            if (onBufferOverflow == BufferOverflow.SUSPEND) CHANNEL_DEFAULT_CAPACITY else 1,
            onBufferOverflow, onUndeliveredElement
        )
        else -> {
            if (capacity == 1 && onBufferOverflow == BufferOverflow.DROP_OLDEST)
                ConflatedChannel(onUndeliveredElement) // conflated implementation is more efficient but appears to work in the same way
            else
                ArrayChannel(capacity, onBufferOverflow, onUndeliveredElement)
        }
    }

@Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.4.0, binary compatibility with earlier versions")
public fun <E> Channel(capacity: Int = RENDEZVOUS): Channel<E> = Channel(capacity)

/**
 * Indicates an attempt to [send][SendChannel.send] to a [isClosedForSend][SendChannel.isClosedForSend] channel
 * that was closed without a cause. A _failed_ channel rethrows the original [close][SendChannel.close] cause
 * exception on send attempts.
 *
 * This exception is a subclass of [IllegalStateException], because, conceptually, it is the sender's responsibility
 * to close the channel and not try to send anything thereafter. Attempts to
 * send to a closed channel indicate a logical error in the sender's code.
 */
public class ClosedSendChannelException(message: String?) : IllegalStateException(message)

/**
 * Indicates an attempt to [receive][ReceiveChannel.receive] from a [isClosedForReceive][ReceiveChannel.isClosedForReceive]
 * channel that was closed without a cause. A _failed_ channel rethrows the original [close][SendChannel.close] cause
 * exception on receive attempts.
 *
 * This exception is a subclass of [NoSuchElementException] to be consistent with plain collections.
 */
public class ClosedReceiveChannelException(message: String?) : NoSuchElementException(message)
