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

import java.io.Closeable

/**
 * Broadcast channel is a non-blocking primitive for communication between the sender and multiple receivers
 * that subscribe for the elements using [open] function and unsubscribe using [SubscriptionReceiveChannel.close]
 * function.
 */
public interface BroadcastChannel<E> : SendChannel<E> {
    /**
     * Subscribes to this [BroadcastChannel] and returns a channel to receive elements from it.
     * The resulting channel shall be [closed][SubscriptionReceiveChannel.close] to unsubscribe from this
     * broadcast channel.
     */
    public fun open(): SubscriptionReceiveChannel<E>
}

/**
 * Return type for [BroadcastChannel.open] that can be used to [receive] elements from the
 * open subscription and to [close] it to unsubscribe.
 */
public interface SubscriptionReceiveChannel<out T> : ReceiveChannel<T>, Closeable {
    /**
     * Closes this subscription.
     */
    public override fun close()
}
