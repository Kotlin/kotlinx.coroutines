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
import kotlin.coroutines.experimental.ContinuationInterceptor
import kotlin.coroutines.experimental.CoroutineContext
import kotlin.coroutines.experimental.startCoroutine

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
 * @suppress **Deprecated**: Renamed to `ProducerScope`.
 */
@Deprecated(message = "Renamed to `ProducerScope`", replaceWith = ReplaceWith("ProducerScope"))
typealias ChannelBuilder<E> = ProducerScope<E>

/**
 * Return type for [produce] coroutine builder.
 */
public interface ProducerJob<out E> : Job, ReceiveChannel<E> {
    /**
     * A reference to the channel that this coroutine is producing.
     * All the [ReceiveChannel] functions on this interface delegate to
     * the channel instance returned by this function.
     */
    val channel: ReceiveChannel<E>
}

/**
 * @suppress **Deprecated**: Renamed to `ProducerJob`.
 */
@Deprecated(message = "Renamed to `ProducerJob`", replaceWith = ReplaceWith("ProducerJob"))
typealias ChannelJob<E> = ProducerJob<E>

/**
 * Launches new coroutine to produce a stream of values by sending them to a channel
 * and returns a reference to the coroutine as a [ProducerJob]. This resulting
 * object can be used to [receive][ReceiveChannel.receive] elements produced by this coroutine.
 *
 * The scope of the coroutine contains [ProducerScope] interface, which implements
 * both [CoroutineScope] and [SendChannel], so that coroutine can invoke
 * [send][SendChannel.send] directly. The channel is [closed][SendChannel.close]
 * when the coroutine completes.
 * The running coroutine is cancelled when the its job is [cancelled][Job.cancel].
 *
 * The [context] for the new coroutine can be explicitly specified.
 * See [CoroutineDispatcher] for the standard context implementations that are provided by `kotlinx.coroutines`.
 * The [context][CoroutineScope.context] of the parent coroutine from its [scope][CoroutineScope] may be used,
 * in which case the [Job] of the resulting coroutine is a child of the job of the parent coroutine.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [DefaultDispatcher] is used.
 *
 * Uncaught exceptions in this coroutine close the channel with this exception as a cause and
 * the resulting channel becomes _failed_, so that any attempt to receive from such a channel throws exception.
 *
 * See [newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
 *
 * @param context context of the coroutine. The default value is [DefaultDispatcher].
 * @param capacity capacity of the channel's buffer (no buffer by default).
 * @param block the coroutine code.
 */
public fun <E> produce(
    context: CoroutineContext = DefaultDispatcher,
    capacity: Int = 0,
    block: suspend ProducerScope<E>.() -> Unit
): ProducerJob<E> {
    val channel = Channel<E>(capacity)
    return ProducerCoroutine(newCoroutineContext(context), channel).apply {
        initParentJob(context[Job])
        block.startCoroutine(this, this)
    }
}

/**
 * @suppress **Deprecated**: Renamed to `produce`.
 */
@Deprecated(message = "Renamed to `produce`", replaceWith = ReplaceWith("produce(context, capacity, block)"))
public fun <E> buildChannel(
    context: CoroutineContext,
    capacity: Int = 0,
    block: suspend ProducerScope<E>.() -> Unit
): ProducerJob<E> =
    produce(context, capacity, block)

private class ProducerCoroutine<E>(parentContext: CoroutineContext, channel: Channel<E>) :
    ChannelCoroutine<E>(parentContext, channel, active = true), ProducerScope<E>, ProducerJob<E>
