/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.Channel.Factory.CONFLATED
import kotlinx.coroutines.channels.Channel.Factory.UNLIMITED
import kotlinx.coroutines.internal.*

/**
 * Broadcast channel is a non-blocking primitive for communication between the sender and multiple receivers
 * that subscribe for the elements using [openSubscription] function and unsubscribe using [ReceiveChannel.cancel]
 * function.
 *
 * See `BroadcastChannel()` factory function for the description of available
 * broadcast channel implementations.
 *
 * **Note: This is an experimental api.** It may be changed in the future updates.
 */
@ExperimentalCoroutinesApi
public interface BroadcastChannel<E> : SendChannel<E> {
    /**
     * Subscribes to this [BroadcastChannel] and returns a channel to receive elements from it.
     * The resulting channel shall be [cancelled][ReceiveChannel.cancel] to unsubscribe from this
     * broadcast channel.
     */
    public fun openSubscription(): ReceiveChannel<E>

    /**
     * Cancels reception of remaining elements from this channel. This function closes the channel with
     * the specified cause (unless it was already closed), removes all buffered sent elements from it,
     * and [cancels][ReceiveChannel.cancel] all open subscriptions.
     * This function returns `true` if the channel was not closed previously, or `false` otherwise.
     *
     * A channel that was cancelled with non-null [cause] is called a _failed_ channel. Attempts to send or
     * receive on a failed channel throw the specified [cause] exception.
     */
    public fun cancel(cause: Throwable? = null): Boolean
}

/**
 * Creates a broadcast channel with the specified buffer capacity.
 *
 * The resulting channel type depends on the specified [capacity] parameter:
 * * when `capacity` positive, but less than [UNLIMITED] -- creates `ArrayBroadcastChannel` with a buffer of given capacity.
 *   **Note:** this channel looses all items that are send to it until the first subscriber appears;
 * * when `capacity` is [CONFLATED] -- creates [ConflatedBroadcastChannel] that conflates back-to-back sends;
 * * otherwise -- throws [IllegalArgumentException].
 *
 * **Note: This is an experimental api.** It may be changed in the future updates.
 */
@ExperimentalCoroutinesApi
public fun <E> BroadcastChannel(capacity: Int): BroadcastChannel<E> =
    when (capacity) {
        0 -> throw IllegalArgumentException("Unsupported 0 capacity for BroadcastChannel")
        UNLIMITED -> throw IllegalArgumentException("Unsupported UNLIMITED capacity for BroadcastChannel")
        CONFLATED -> ConflatedBroadcastChannel()
        else -> ArrayBroadcastChannel(capacity)
    }
