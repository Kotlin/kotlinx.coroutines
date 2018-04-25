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
import kotlin.coroutines.experimental.*

/**
 * Scope for [produce] coroutine builder.
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
 * See [newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
 *
 * @param context context of the coroutine. The default value is [DefaultDispatcher].
 * @param capacity capacity of the channel's buffer (no buffer by default).
 * @param parent explicitly specifies the parent job, overrides job from the [context] (if any).*
 * @param onCompletion optional completion handler for the producer coroutine (see [Job.invokeOnCompletion]).
 * @param block the coroutine code.
 */
public fun <E> produce(
    context: CoroutineContext = DefaultDispatcher,
    capacity: Int = 0,
    parent: Job? = null,
    onCompletion: CompletionHandler? = null,
    block: suspend ProducerScope<E>.() -> Unit
): ReceiveChannel<E> {
    val channel = Channel<E>(capacity)
    val newContext = newCoroutineContext(context, parent)
    val coroutine = ProducerCoroutine(newContext, channel)
    if (onCompletion != null) coroutine.invokeOnCompletion(handler = onCompletion)
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
    return coroutine
}

/** @suppress **Deprecated**: Binary compatibility */
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <E> produce(
    context: CoroutineContext = DefaultDispatcher,
    capacity: Int = 0,
    parent: Job? = null,
    block: suspend ProducerScope<E>.() -> Unit
): ReceiveChannel<E> = produce(context, capacity, parent, block = block)

/** @suppress **Deprecated**: Binary compatibility */
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <E> produce(
    context: CoroutineContext = DefaultDispatcher,
    capacity: Int = 0,
    block: suspend ProducerScope<E>.() -> Unit
): ProducerJob<E> =
    produce(context, capacity, block = block) as ProducerJob<E>

/**
 * @suppress **Deprecated**: Renamed to `produce`.
 */
@Deprecated(message = "Renamed to `produce`", replaceWith = ReplaceWith("produce(context, capacity, block)"))
public fun <E> buildChannel(
    context: CoroutineContext,
    capacity: Int = 0,
    block: suspend ProducerScope<E>.() -> Unit
): ProducerJob<E> =
    produce(context, capacity, block = block) as ProducerJob<E>

private class ProducerCoroutine<E>(
    parentContext: CoroutineContext, channel: Channel<E>
) : ChannelCoroutine<E>(parentContext, channel, active = true), ProducerScope<E>, ProducerJob<E> {
    override fun onCancellationInternal(exceptionally: CompletedExceptionally?) {
        val cause = exceptionally?.cause
        val processed = when (exceptionally) {
            // producer coroutine was cancelled -- cancel channel, but without cause if it was closed without cause
            is Cancelled -> _channel.cancel(if (cause is CancellationException) null else cause)
            else -> _channel.close(cause) // producer coroutine has completed -- close channel
        }
        if (!processed && cause != null)
            handleCoroutineException(context, cause)
    }
}
