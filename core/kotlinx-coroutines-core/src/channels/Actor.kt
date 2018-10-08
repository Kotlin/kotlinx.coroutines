/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:UseExperimental(ExperimentalTypeInference::class)

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.Channel.Factory.UNLIMITED
import kotlinx.coroutines.intrinsics.*
import kotlinx.coroutines.selects.*
import kotlin.coroutines.*
import kotlin.experimental.*

/**
 * Scope for [actor][GlobalScope.actor] coroutine builder.
 *
 * **Note: This API will become obsolete in future updates with introduction of complex actors.**
 *           See [issue #87](https://github.com/Kotlin/kotlinx.coroutines/issues/87).
 */
@ObsoleteCoroutinesApi
public interface ActorScope<E> : CoroutineScope, ReceiveChannel<E> {
    /**
     * A reference to the mailbox channel that this coroutine [receives][receive] messages from.
     * It is provided for convenience, so that the code in the coroutine can refer
     * to the channel as `channel` as apposed to `this`.
     * All the [ReceiveChannel] functions on this interface delegate to
     * the channel instance returned by this function.
     */
    val channel: Channel<E>
}

/**
 * Launches new coroutine that is receiving messages from its mailbox channel
 * and returns a reference to its mailbox channel as a [SendChannel]. The resulting
 * object can be used to [send][SendChannel.send] messages to this coroutine.
 *
 * The scope of the coroutine contains [ActorScope] interface, which implements
 * both [CoroutineScope] and [ReceiveChannel], so that coroutine can invoke
 * [receive][ReceiveChannel.receive] directly. The channel is [closed][SendChannel.close]
 * when the coroutine completes.
 *
 * Coroutine context is inherited from a [CoroutineScope], additional context elements can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * The parent job is inherited from a [CoroutineScope] as well, but it can also be overridden
 * with corresponding [coroutineContext] element.
 *
 * By default, the coroutine is immediately scheduled for execution.
 * Other options can be specified via `start` parameter. See [CoroutineStart] for details.
 * An optional [start] parameter can be set to [CoroutineStart.LAZY] to start coroutine _lazily_. In this case,
 * it will be started implicitly on the first message
 * [sent][SendChannel.send] to this actors's mailbox channel.
 *
 * Uncaught exceptions in this coroutine close the channel with this exception as a cause and
 * the resulting channel becomes _failed_, so that any attempt to send to such a channel throws exception.
 *
 * The kind of the resulting channel depends on the specified [capacity] parameter.
 * See [Channel] interface documentation for details.
 *
 * See [newCoroutineContext][CoroutineScope.newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
 *
 * ### Using actors
 *
 * A typical usage of the actor builder looks like this:
 *
 * ```
 * val c = actor {
 *     // initialize actor's state
 *     for (msg in channel) {
 *         // process message here
 *     }
 * }
 * // send messages to the actor
 * c.send(...)
 * ...
 * // stop the actor when it is no longer needed
 * c.close()
 * ```
 *
 * ### Stopping and cancelling actors
 *
 * When the inbox channel of the actor is [closed][SendChannel.close] it sends a special "close token" to the actor.
 * The actor still processes all the messages that were already sent and then "`for (msg in channel)`" loop terminates
 * and the actor completes.
 *
 * If the actor needs to be aborted without processing all the messages that were already sent to it, then
 * it shall be created with a parent job:
 *
 * ```
 * val job = Job()
 * val c = actor(context = job) {  ... }
 * ...
 * // abort the actor
 * job.cancel()
 * ```
 *
 * When actor's parent job is [cancelled][Job.cancel], then actor's job becomes cancelled. It means that
 * "`for (msg in channel)`" and other cancellable suspending functions throw [CancellationException] and actor
 * completes without processing remaining messages.
 *
 * **Note: This API will become obsolete in future updates with introduction of complex actors.**
 *           See [issue #87](https://github.com/Kotlin/kotlinx.coroutines/issues/87).
 *
 * @param context additional to [CoroutineScope.coroutineContext] context of the coroutine.
 * @param capacity capacity of the channel's buffer (no buffer by default).
 * @param start coroutine start option. The default value is [CoroutineStart.DEFAULT].
 * @param onCompletion optional completion handler for the actor coroutine (see [Job.invokeOnCompletion]).
 * @param block the coroutine code.
 */
@ObsoleteCoroutinesApi
@BuilderInference
public fun <E> CoroutineScope.actor(
    context: CoroutineContext = EmptyCoroutineContext,
    capacity: Int = 0,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    onCompletion: CompletionHandler? = null,
    block: suspend ActorScope<E>.() -> Unit
): SendChannel<E> {
    val newContext = newCoroutineContext(context)
    val channel = Channel<E>(capacity)
    val coroutine = if (start.isLazy)
        LazyActorCoroutine(newContext, channel, block) else
        ActorCoroutine(newContext, channel, active = true)
    if (onCompletion != null) coroutine.invokeOnCompletion(handler = onCompletion)
    coroutine.start(start, coroutine, block)
    return coroutine
}

private open class ActorCoroutine<E>(
    parentContext: CoroutineContext,
    channel: Channel<E>,
    active: Boolean
) : ChannelCoroutine<E>(parentContext, channel, active), ActorScope<E> {
    override fun onCancellation(cause: Throwable?) {
        _channel.cancel(cause)
    }

    override val cancelsParent: Boolean get() = true
    override fun handleJobException(exception: Throwable) = handleExceptionViaHandler(parentContext, exception)
}

private class LazyActorCoroutine<E>(
    parentContext: CoroutineContext,
    channel: Channel<E>,
    private val block: suspend ActorScope<E>.() -> Unit
) : ActorCoroutine<E>(parentContext, channel, active = false),
    SelectClause2<E, SendChannel<E>> {
    override fun onStart() {
        block.startCoroutineCancellable(this, this)
    }

    override suspend fun send(element: E) {
        start()
        return super.send(element)
    }

    override fun offer(element: E): Boolean {
        start()
        return super.offer(element)
    }

    override val onSend: SelectClause2<E, SendChannel<E>>
        get() = this

    // registerSelectSend
    override fun <R> registerSelectClause2(select: SelectInstance<R>, param: E, block: suspend (SendChannel<E>) -> R) {
        start()
        super.onSend.registerSelectClause2(select, param, block)
    }
}
