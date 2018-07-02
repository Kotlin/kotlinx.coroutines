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
) : BroadcastChannel<E> =
    broadcast(Unconfined, capacity = capacity, start = start, onCompletion = consumes()) {
        for (e in this@broadcast) {
            send(e)
        }
    }

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
 * The [context] for the new coroutine can be explicitly specified.
 * See [CoroutineDispatcher] for the standard context implementations that are provided by `kotlinx.coroutines`.
 * The [coroutineContext] of the parent coroutine may be used,
 * in which case the [Job] of the resulting coroutine is a child of the job of the parent coroutine.
 * The parent job may be also explicitly specified using [parent] parameter.
 *
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [DefaultDispatcher] is used.
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
 * @param context context of the coroutine. The default value is [DefaultDispatcher].
 * @param capacity capacity of the channel's buffer (1 by default).
 * @param start coroutine start option. The default value is [CoroutineStart.LAZY].
 * @param parent explicitly specifies the parent job, overrides job from the [context] (if any).*
 * @param onCompletion optional completion handler for the producer coroutine (see [Job.invokeOnCompletion]).
 * @param block the coroutine code.
 */
public fun <E> broadcast(
    context: CoroutineContext = DefaultDispatcher,
    capacity: Int = 1,
    start: CoroutineStart = CoroutineStart.LAZY,
    parent: Job? = null,
    onCompletion: CompletionHandler? = null,
    block: suspend ProducerScope<E>.() -> Unit
): BroadcastChannel<E> {
    val channel = BroadcastChannel<E>(capacity)
    val newContext = newCoroutineContext(context, parent)
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
    override val channel: SendChannel<E>
        get() = this

    public override fun cancel(cause: Throwable?): Boolean = super.cancel(cause)

    override fun onCancellationInternal(exceptionally: CompletedExceptionally?) {
        val cause = exceptionally?.cause
        val processed = when (exceptionally) {
            is Cancelled -> _channel.cancel(cause) // producer coroutine was cancelled -- cancel channel
            else -> _channel.close(cause) // producer coroutine has completed -- close channel
        }
        if (!processed && cause != null)
            handleCoroutineException(context, cause)
    }

    // Workaround for KT-23094
    override suspend fun send(element: E) = _channel.send(element)
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

