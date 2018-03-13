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

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.intrinsics.*
import kotlinx.coroutines.experimental.selects.*
import kotlin.coroutines.experimental.*

/**
 * Scope for [actor] coroutine builder.
 */
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
 * @suppress **Deprecated**: Use `SendChannel`.
 */
@Deprecated(message = "Use `SendChannel`", replaceWith = ReplaceWith("SendChannel"))
interface ActorJob<in E> : SendChannel<E> {
    @Deprecated(message = "Use SendChannel itself")
    val channel: SendChannel<E>
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
 * The [context] for the new coroutine can be explicitly specified.
 * See [CoroutineDispatcher] for the standard context implementations that are provided by `kotlinx.coroutines`.
 * The [context][CoroutineScope.context] of the parent coroutine from its [scope][CoroutineScope] may be used,
 * in which case the [Job] of the resulting coroutine is a child of the job of the parent coroutine.
 * The parent job may be also explicitly specified using [parent] parameter.
 *
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [DefaultDispatcher] is used.
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
 * See [newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
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
 * val c = actor(parent = job) {  ... }
 * ...
 * // abort the actor
 * job.cancel()
 * ```
 *
 * When actor's parent job is [cancelled][Job.cancel], then actor's job becomes cancelled. It means that
 * "`for (msg in channel)`" and other cancellable suspending functions throw [CancellationException] and actor
 * completes without processing remaining messages.
 *
 * @param context context of the coroutine. The default value is [DefaultDispatcher].
 * @param capacity capacity of the channel's buffer (no buffer by default).
 * @param start coroutine start option. The default value is [CoroutineStart.DEFAULT].
 * @param parent explicitly specifies the parent job, overrides job from the [context] (if any).*
 * @param onCompletion optional completion handler for the actor coroutine (see [Job.invokeOnCompletion]).
 * @param block the coroutine code.
 */
public fun <E> actor(
    context: CoroutineContext = DefaultDispatcher,
    capacity: Int = 0,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    parent: Job? = null,
    onCompletion: CompletionHandler? = null,
    block: suspend ActorScope<E>.() -> Unit
): SendChannel<E> {
    val newContext = newCoroutineContext(context, parent)
    val channel = Channel<E>(capacity)
    val coroutine = if (start.isLazy)
        LazyActorCoroutine(newContext, channel, block) else
        ActorCoroutine(newContext, channel, active = true)
    if (onCompletion != null) coroutine.invokeOnCompletion(handler = onCompletion)
    coroutine.start(start, coroutine, block)
    return coroutine
}

/** @suppress **Deprecated**: Binary compatibility */
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <E> actor(
    context: CoroutineContext = DefaultDispatcher,
    capacity: Int = 0,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    parent: Job? = null,
    block: suspend ActorScope<E>.() -> Unit
): SendChannel<E> = actor(context, capacity, start, parent, block = block)

/** @suppress **Deprecated**: Binary compatibility */
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <E> actor(
    context: CoroutineContext = DefaultDispatcher,
    capacity: Int = 0,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend ActorScope<E>.() -> Unit
): ActorJob<E> =
    actor(context, capacity, start, block = block) as ActorJob<E>

private open class ActorCoroutine<E>(
    parentContext: CoroutineContext,
    channel: Channel<E>,
    active: Boolean
) : ChannelCoroutine<E>(parentContext, channel, active), ActorScope<E>, ActorJob<E> {
    override fun onCancellation(cause: Throwable?) {
        if (!_channel.cancel(cause) && cause != null)
            handleCoroutineException(context, cause)
    }
}

private class LazyActorCoroutine<E>(
    parentContext: CoroutineContext,
    channel: Channel<E>,
    private val block: suspend ActorScope<E>.() -> Unit
) : ActorCoroutine<E>(parentContext, channel, active = false), SelectClause2<E, SendChannel<E>> {
    override fun onStart() {
        block.startCoroutineCancellable(this, this)
    }

    suspend override fun send(element: E) {
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

