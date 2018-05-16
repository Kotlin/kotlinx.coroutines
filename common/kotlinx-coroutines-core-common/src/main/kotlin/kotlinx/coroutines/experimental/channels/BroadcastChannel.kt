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
import kotlinx.coroutines.experimental.channels.Channel.Factory.CONFLATED
import kotlinx.coroutines.experimental.channels.Channel.Factory.UNLIMITED
import kotlinx.coroutines.experimental.internal.Closeable
import kotlinx.coroutines.experimental.internalAnnotations.*

/**
 * Broadcast channel is a non-blocking primitive for communication between the sender and multiple receivers
 * that subscribe for the elements using [openSubscription] function and unsubscribe using [ReceiveChannel.cancel]
 * function.
 *
 * See `BroadcastChannel()` factory function for the description of available
 * broadcast channel implementations.
 */
public interface BroadcastChannel<E> : SendChannel<E> {
    /**
     * Factory for broadcast channels.
     * @suppress **Deprecated**
     */
    public companion object Factory {
        /**
         * Creates a broadcast channel with the specified buffer capacity.
         * @suppress **Deprecated**
         */
        @Deprecated("Replaced with top-level function", level = DeprecationLevel.HIDDEN)
        public operator fun <E> invoke(capacity: Int): BroadcastChannel<E> = BroadcastChannel(capacity)
    }

    /**
     * Subscribes to this [BroadcastChannel] and returns a channel to receive elements from it.
     * The resulting channel shall be [cancelled][ReceiveChannel.cancel] to unsubscribe from this
     * broadcast channel.
     */
    @Suppress("CONFLICTING_OVERLOADS")
    public fun openSubscription(): ReceiveChannel<E>

    /**
     * @suppress **Deprecated**: Return type changed to `ReceiveChannel`, this one left here for binary compatibility.
     */
    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Return type changed to `ReceiveChannel`, this one left here for binary compatibility")
    @Suppress("CONFLICTING_OVERLOADS")
    @JsName("openSubscriptionDeprecated")
    public fun openSubscription(): SubscriptionReceiveChannel<E> = openSubscription() as SubscriptionReceiveChannel<E>

    /**
     * @suppress **Deprecated**: Renamed to [openSubscription]
     */
    @Deprecated(message = "Renamed to `openSubscription`",
        replaceWith = ReplaceWith("openSubscription()"))
    public fun open(): SubscriptionReceiveChannel<E> = openSubscription() as SubscriptionReceiveChannel<E>
}

/**
 * Creates a broadcast channel with the specified buffer capacity.
 *
 * The resulting channel type depends on the specified [capacity] parameter:
 * * when `capacity` positive, but less than [UNLIMITED] -- creates [ArrayBroadcastChannel];
 * * when `capacity` is [CONFLATED] -- creates [ConflatedBroadcastChannel] that conflates back-to-back sends;
 * * otherwise -- throws [IllegalArgumentException].
 */
public fun <E> BroadcastChannel(capacity: Int): BroadcastChannel<E> =
    when (capacity) {
        0 -> throw IllegalArgumentException("Unsupported 0 capacity for BroadcastChannel")
        UNLIMITED -> throw IllegalArgumentException("Unsupported UNLIMITED capacity for BroadcastChannel")
        CONFLATED -> ConflatedBroadcastChannel()
        else -> ArrayBroadcastChannel(capacity)
    }

/**
 * Return type for [BroadcastChannel.openSubscription] that can be used to [receive] elements from the
 * open subscription and to [close] it to unsubscribe.
 *
 * Note, that invocation of [cancel] also closes subscription.
 */
@Deprecated("Deprecated in favour of `ReceiveChannel`", replaceWith = ReplaceWith("ReceiveChannel"))
public interface SubscriptionReceiveChannel<out T> : ReceiveChannel<T>, Closeable {
    /**
     * Closes this subscription. This is a synonym for [cancel].
     */
    @Deprecated("Use `cancel`", replaceWith = ReplaceWith("cancel()"))
    public override fun close() { cancel() }
}
