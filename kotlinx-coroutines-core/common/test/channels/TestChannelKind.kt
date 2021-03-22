/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*

enum class TestChannelKind(
    val capacity: Int,
    private val description: String,
    val viaBroadcast: Boolean = false
) {
    RENDEZVOUS(0, "RendezvousChannel"),
    ARRAY_1(1, "ArrayChannel(1)"),
    ARRAY_2(2, "ArrayChannel(2)"),
    ARRAY_10(10, "ArrayChannel(10)"),
    LINKED_LIST(Channel.UNLIMITED, "LinkedListChannel"),
    CONFLATED(Channel.CONFLATED, "ConflatedChannel"),
    ARRAY_1_BROADCAST(1, "ArrayBroadcastChannel(1)", viaBroadcast = true),
    ARRAY_10_BROADCAST(10, "ArrayBroadcastChannel(10)", viaBroadcast = true),
    CONFLATED_BROADCAST(Channel.CONFLATED, "ConflatedBroadcastChannel", viaBroadcast = true)
    ;

    fun <T> create(onUndeliveredElement: ((T) -> Unit)? = null): Channel<T> = when {
        viaBroadcast && onUndeliveredElement != null -> error("Broadcast channels to do not support onUndeliveredElement")
        viaBroadcast -> ChannelViaBroadcast(BroadcastChannel(capacity))
        else -> Channel(capacity, onUndeliveredElement = onUndeliveredElement)
    }

    val isConflated get() = capacity == Channel.CONFLATED
    override fun toString(): String = description
}

private class ChannelViaBroadcast<E>(
    private val broadcast: BroadcastChannel<E>
): Channel<E>, SendChannel<E> by broadcast {
    val sub = broadcast.openSubscription()

    override val isClosedForReceive: Boolean get() = sub.isClosedForReceive
    override val isEmpty: Boolean get() = sub.isEmpty

    override suspend fun receive(): E = sub.receive()
    override suspend fun receiveOrNull(): E? = sub.receiveOrNull()
    override suspend fun receiveCatching(): ChannelResult<E> = sub.receiveCatching()
    override fun iterator(): ChannelIterator<E> = sub.iterator()
    override fun tryReceive(): ChannelResult<E> = sub.tryReceive()

    override fun cancel(cause: CancellationException?) = sub.cancel(cause)

    // implementing hidden method anyway, so can cast to an internal class
    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.2.0, binary compatibility with versions <= 1.1.x")
    override fun cancel(cause: Throwable?): Boolean = (sub as AbstractChannel).cancelInternal(cause)

    override val onReceive: SelectClause1<E>
        get() = sub.onReceive
    override val onReceiveOrNull: SelectClause1<E?>
        get() = sub.onReceiveOrNull
    override val onReceiveCatching: SelectClause1<ChannelResult<E>>
        get() = sub.onReceiveCatching
}
