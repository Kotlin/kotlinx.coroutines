/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.Channel.Factory.UNLIMITED
import kotlin.coroutines.experimental.*

/**
 * Scope for [produce][CoroutineScope.produce] coroutine builder.
 */
public interface ProducerScope<in E> : CoroutineScope, SendChannel<E> {
    /**
     * A reference to the channel that this coroutine [sends][send] elements to.
     * It is provided for convenience, so that the code in the coroutine can refer
     * to the channel as `channel` as apposed to `this`.
     * All the [SendChannel] functions on this interface delegate to
     * the channel instance returned by this function.
     */
    val channel: SendChannel<E>
}

/**
 * @suppress **Deprecated**: Use `ReceiveChannel`.
 */
@Deprecated(message = "Use `ReceiveChannel`", replaceWith = ReplaceWith("ReceiveChannel"))
@Suppress("MULTIPLE_DEFAULTS_INHERITED_FROM_SUPERTYPES_WHEN_NO_EXPLICIT_OVERRIDE")
interface ProducerJob<out E> : ReceiveChannel<E>, Job {
    @Deprecated(message = "Use ReceiveChannel itself")
    val channel: ReceiveChannel<E>
}

/**
 * Launches new coroutine to produce a stream of values by sending them to a channel
 * and returns a reference to the coroutine as a [ReceiveChannel]. This resulting
 * object can be used to [receive][ReceiveChannel.receive] elements produced by this coroutine.
 *
 * The scope of the coroutine contains [ProducerScope] interface, which implements
 * both [CoroutineScope] and [SendChannel], so that coroutine can invoke
 * [send][SendChannel.send] directly. The channel is [closed][SendChannel.close]
 * when the coroutine completes.
 * The running coroutine is cancelled when its receive channel is [cancelled][ReceiveChannel.cancel].
 *
 * Coroutine context is inherited from a [CoroutineScope], additional context elements can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * The parent job is inherited from a [CoroutineScope] as well, but it can also be overridden
 * with corresponding [coroutineContext] element.
 *
 * Uncaught exceptions in this coroutine close the channel with this exception as a cause and
 * the resulting channel becomes _failed_, so that any attempt to receive from such a channel throws exception.
 *
 * The kind of the resulting channel depends on the specified [capacity] parameter:
 * * when `capacity` is 0 (default) -- uses [RendezvousChannel] without a buffer;
 * * when `capacity` is [Channel.UNLIMITED] -- uses [LinkedListChannel] with buffer of unlimited size;
 * * when `capacity` is [Channel.CONFLATED] -- uses [ConflatedChannel] that conflates back-to-back sends;
 * * when `capacity` is positive, but less than [UNLIMITED] -- uses [ArrayChannel] with a buffer of the specified `capacity`;
 * * otherwise -- throws [IllegalArgumentException].
 *
 * See [newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
 *
 * @param context additional to [CoroutineScope.coroutineContext] context of the coroutine.
 * @param capacity capacity of the channel's buffer (no buffer by default).
 * @param onCompletion optional completion handler for the producer coroutine (see [Job.invokeOnCompletion]).
 * @param block the coroutine code.
 */
public fun <E> CoroutineScope.produce(
    context: CoroutineContext = EmptyCoroutineContext,
    capacity: Int = 0,
    onCompletion: CompletionHandler? = null,
    block: suspend ProducerScope<E>.() -> Unit
): ReceiveChannel<E> {
    val channel = Channel<E>(capacity)
    val newContext = newCoroutineContext(context)
    val coroutine = ProducerCoroutine(newContext, channel)
    if (onCompletion != null) coroutine.invokeOnCompletion(handler = onCompletion)
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
    return coroutine
}

/**
 * Launches new coroutine to produce a stream of values by sending them to a channel
 * and returns a reference to the coroutine as a [ReceiveChannel].
 * @suppress **Deprecated** Use [CoroutineScope.produce] instead.
 */
@Deprecated(
    message = "Standalone coroutine builders are deprecated, use extensions on CoroutineScope instead",
    replaceWith = ReplaceWith("GlobalScope.produce(context, capacity, onCompletion, block)",
        imports = ["kotlinx.coroutines.experimental.GlobalScope", "kotlinx.coroutines.experimental.channels.produce"])
)
public fun <E> produce(
    context: CoroutineContext = Dispatchers.Default,
    capacity: Int = 0,
    onCompletion: CompletionHandler? = null,
    block: suspend ProducerScope<E>.() -> Unit
): ReceiveChannel<E> =
    GlobalScope.produce(context, capacity, onCompletion, block)

/**
 * Launches new coroutine to produce a stream of values by sending them to a channel
 * and returns a reference to the coroutine as a [ReceiveChannel].
 * @suppress **Deprecated** Use [CoroutineScope.produce] instead.
 */
@Deprecated(
    message = "Standalone coroutine builders are deprecated, use extensions on CoroutineScope instead",
    replaceWith = ReplaceWith("GlobalScope.produce(context + parent, capacity, onCompletion, block)",
        imports = ["kotlinx.coroutines.experimental.GlobalScope", "kotlinx.coroutines.experimental.channels.produce"])
)
public fun <E> produce(
    context: CoroutineContext = Dispatchers.Default,
    capacity: Int = 0,
    parent: Job? = null,
    onCompletion: CompletionHandler? = null,
    block: suspend ProducerScope<E>.() -> Unit
): ReceiveChannel<E> =
    GlobalScope.produce(context + (parent ?: EmptyCoroutineContext), capacity, onCompletion, block)

/** @suppress **Deprecated**: Binary compatibility */
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <E> produce(
    context: CoroutineContext = Dispatchers.Default,
    capacity: Int = 0,
    parent: Job? = null,
    block: suspend ProducerScope<E>.() -> Unit
): ReceiveChannel<E> = GlobalScope.produce(context + (parent ?: EmptyCoroutineContext), capacity, block = block)

/** @suppress **Deprecated**: Binary compatibility */
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <E> produce(
    context: CoroutineContext = Dispatchers.Default,
    capacity: Int = 0,
    block: suspend ProducerScope<E>.() -> Unit
): ProducerJob<E> =
    GlobalScope.produce(context, capacity, block = block) as ProducerJob<E>

/**
 * @suppress **Deprecated**: Renamed to `produce`.
 */
@Deprecated(message = "Renamed to `produce`", replaceWith = ReplaceWith("produce(context, capacity, block)"))
public fun <E> buildChannel(
    context: CoroutineContext,
    capacity: Int = 0,
    block: suspend ProducerScope<E>.() -> Unit
): ProducerJob<E> =
    GlobalScope.produce(context, capacity, block = block) as ProducerJob<E>

private class ProducerCoroutine<E>(
    parentContext: CoroutineContext, channel: Channel<E>
) : ChannelCoroutine<E>(parentContext, channel, active = true), ProducerScope<E>, ProducerJob<E> {

    override val isActive: Boolean
        get() = super<ChannelCoroutine>.isActive

    override fun onCancellationInternal(exceptionally: CompletedExceptionally?) {
        val cause = exceptionally?.cause
        val processed = when (exceptionally) {
            // producer coroutine was cancelled -- cancel channel, but without cause if it was closed without cause
            is Cancelled -> _channel.cancel(if (cause is CancellationException) null else cause)
            else -> _channel.close(cause) // producer coroutine has completed -- close channel
        }
        if (!processed && cause != null)
            handleCoroutineException(context, cause, this)
    }
}
