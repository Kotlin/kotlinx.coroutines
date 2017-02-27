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

import kotlinx.coroutines.experimental.CoroutineDispatcher
import kotlinx.coroutines.experimental.CoroutineScope
import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.newCoroutineContext
import kotlin.coroutines.experimental.CoroutineContext
import kotlin.coroutines.experimental.startCoroutine

/**
 * Scope for [actor] coroutine builder.
 */
public interface ActorScope<out E> : CoroutineScope, ReceiveChannel<E> {
    /**
     * A reference to the mailbox channel that this coroutine [receives][receive] messages from.
     * It is provided for convenience, so that the code in the coroutine can refer
     * to the channel as `channel` as apposed to `this`.
     * All the [ReceiveChannel] functions on this interface delegate to
     * the channel instance returned by this function.
     */
    val channel: ReceiveChannel<E>
}

/**
 * Return type for [actor] coroutine builder.
 */
public interface ActorJob<in E> : Job, SendChannel<E> {
    /**
     * A reference to the mailbox channel that this coroutine is receiving messages from.
     * All the [SendChannel] functions on this interface delegate to
     * the channel instance returned by this function.
     */
    val channel: SendChannel<E>
}

/**
 * Launches new coroutine that is receiving messages from its mailbox channel
 * and returns a reference to the coroutine as an [ActorJob]. The resulting
 * object can be used to [send][SendChannel.send] messages to this coroutine.
 *
 * The scope of the coroutine contains [ActorScope] interface, which implements
 * both [CoroutineScope] and [ReceiveChannel], so that coroutine can invoke
 * [receive][ReceiveChannel.receive] directly. The channel is [closed][SendChannel.close]
 * when the coroutine completes.
 * The running coroutine is cancelled when the its job is [cancelled][Job.cancel].
 *
 * The [context] for the new coroutine must be explicitly specified.
 * See [CoroutineDispatcher] for the standard [context] implementations that are provided by `kotlinx.coroutines`.
 * The [context][CoroutineScope.context] of the parent coroutine from its [scope][CoroutineScope] may be used,
 * in which case the [Job] of the resulting coroutine is a child of the job of the parent coroutine.
 *
 * Uncaught exceptions in this coroutine close the channel with this exception as a cause and
 * the resulting channel becomes _failed_, so that any attempt to send to such a channel throws exception.
 *
 * See [newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
 *
 * @param context context of the coroutine
 * @param capacity capacity of the channel's buffer (no buffer by default)
 * @param block the coroutine code
 */
public fun <E> actor(
    context: CoroutineContext,
    capacity: Int = 0,
    block: suspend ActorScope<E>.() -> Unit
): ActorJob<E> {
    val channel = Channel<E>(capacity)
    return ActorCoroutine(newCoroutineContext(context), channel).apply {
        initParentJob(context[Job])
        block.startCoroutine(this, this)
    }
}

private class ActorCoroutine<E>(parentContext: CoroutineContext, channel: Channel<E>) :
    ChannelCoroutine<E>(parentContext, channel), ActorScope<E>, ActorJob<E>
