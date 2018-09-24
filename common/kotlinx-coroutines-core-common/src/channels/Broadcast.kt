/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.Channel.Factory.CONFLATED
import kotlinx.coroutines.experimental.channels.Channel.Factory.UNLIMITED
import kotlinx.coroutines.experimental.intrinsics.*
import kotlin.coroutines.experimental.*

/**
 * Broadcasts all elements of the channel.
 *
 * @param capacity capacity of the channel's buffer (1 by default).
 * @param start coroutine start option. The default value is [CoroutineStart.LAZY].
 */
fun <E> ReceiveChannel<E>.broadcast(
    capacity: Int = 1,
    start: CoroutineStart = CoroutineStart.LAZY
): BroadcastChannel<E> =
    GlobalScope.broadcast(Dispatchers.Unconfined, capacity = capacity, start = start, onCompletion = consumes()) {
        for (e in this@broadcast) {
            send(e)
        }
    }

/**
 * Launches new coroutine to produce a stream of values by sending them to a broadcast channel.
 * @suppress **Deprecated**: use [CoroutineScope.broadcast] instead.
 */
@Deprecated(
    message = "Standalone coroutine builders are deprecated, use extensions on CoroutineScope instead",
    replaceWith = ReplaceWith(
        "GlobalScope.broadcast(context + parent, capacity, start, onCompletion, block)",
        imports = ["kotlinx.coroutines.experimental.GlobalScope", "kotlinx.coroutines.experimental.channels.broadcast"]
    )
)
public fun <E> broadcast(
    context: CoroutineContext = Dispatchers.Default,
    capacity: Int = 1,
    start: CoroutineStart = CoroutineStart.LAZY,
    parent: Job? = null,
    onCompletion: CompletionHandler? = null,
    block: suspend ProducerScope<E>.() -> Unit
): BroadcastChannel<E> =
    GlobalScope.broadcast(context + (parent ?: EmptyCoroutineContext), capacity, start, onCompletion, block)

/**
 * Launches new coroutine to produce a stream of values by sending them to a broadcast channel
 * and returns a reference to the coroutine as a [BroadcastChannel]. The resulting
 * object can be used to [subscribe][BroadcastChannel.openSubscription] to elements produced by this coroutine.
 *
 * The scope of the coroutine contains [ProducerScope] interface, which implements
 * both [CoroutineScope] and [SendChannel], so that coroutine can invoke
 * [send][SendChannel.send] directly. The channel is [closed][SendChannel.close]
 * when the coroutine completes.
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
 * * when `capacity` positive (1 by default), but less than [UNLIMITED] -- uses [ArrayBroadcastChannel]
 * * when `capacity` is [CONFLATED] -- uses [ConflatedBroadcastChannel] that conflates back-to-back sends;
 * * otherwise -- throws [IllegalArgumentException].
 *
 * **Note:** By default, the coroutine does not start until the first subscriber appears via [BroadcastChannel.openSubscription]
 * as [start] parameter has a value of [CoroutineStart.LAZY] by default.
 * This ensures that the first subscriber does not miss any sent elements.
 * However, later subscribers may miss elements.
 *
 * See [newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
 *
 * @param context additional to [CoroutineScope.coroutineContext] context of the coroutine.
 * @param capacity capacity of the channel's buffer (1 by default).
 * @param start coroutine start option. The default value is [CoroutineStart.LAZY].
 * @param onCompletion optional completion handler for the producer coroutine (see [Job.invokeOnCompletion]).
 * @param block the coroutine code.
 */
public fun <E> CoroutineScope.broadcast(
    context: CoroutineContext = EmptyCoroutineContext,
    capacity: Int = 1,
    start: CoroutineStart = CoroutineStart.LAZY,
    onCompletion: CompletionHandler? = null,
    block: suspend ProducerScope<E>.() -> Unit
): BroadcastChannel<E> {
    val newContext = newCoroutineContext(context)
    val channel = BroadcastChannel<E>(capacity)
    val coroutine = if (start.isLazy)
        LazyBroadcastCoroutine(newContext, channel, block) else
        BroadcastCoroutine(newContext, channel, active = true)
    if (onCompletion != null) coroutine.invokeOnCompletion(handler = onCompletion)
    coroutine.start(start, coroutine, block)
    return coroutine
}

private open class BroadcastCoroutine<E>(
    parentContext: CoroutineContext,
    protected val _channel: BroadcastChannel<E>,
    active: Boolean
) : AbstractCoroutine<Unit>(parentContext, active), ProducerScope<E>, BroadcastChannel<E> by _channel {

    override val isActive: Boolean get() = super<AbstractCoroutine>.isActive

    override val channel: SendChannel<E>
        get() = this

    override fun cancel(): Boolean = super.cancel()
    public override fun cancel(cause: Throwable?): Boolean = super.cancel(cause)

    override fun onCancellationInternal(exceptionally: CompletedExceptionally?) {
        val cause = exceptionally?.cause
        val processed = when (exceptionally) {
            is Cancelled -> _channel.cancel(cause) // producer coroutine was cancelled -- cancel channel
            else -> _channel.close(cause) // producer coroutine has completed -- close channel
        }
        if (!processed && cause != null)
            handleCoroutineException(context, cause, this)
    }
}

private class LazyBroadcastCoroutine<E>(
    parentContext: CoroutineContext,
    channel: BroadcastChannel<E>,
    private val block: suspend ProducerScope<E>.() -> Unit
) : BroadcastCoroutine<E>(parentContext, channel, active = false) {
    override fun openSubscription(): ReceiveChannel<E> {
        // open subscription _first_
        val subscription = _channel.openSubscription()
        // then start coroutine
        start()
        return subscription
    }

    override fun onStart() {
        block.startCoroutineCancellable(this, this)
    }
}
