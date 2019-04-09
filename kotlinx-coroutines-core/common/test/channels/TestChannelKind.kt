/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*

enum class TestChannelKind {
    RENDEZVOUS {
        override fun create(): Channel<Int> = Channel(Channel.RENDEZVOUS)
        override fun toString(): String = "RendezvousChannel"
    },
    ARRAY_1 {
        override fun create(): Channel<Int> = Channel(1)
        override fun toString(): String = "ArrayChannel(1)"
    },
    ARRAY_10 {
        override fun create(): Channel<Int> = Channel(10)
        override fun toString(): String = "ArrayChannel(10)"
    },
    LINKED_LIST {
        override fun create(): Channel<Int> = Channel(Channel.UNLIMITED)
        override fun toString(): String = "LinkedListChannel"
    },
    CONFLATED {
        override fun create(): Channel<Int> = Channel(Channel.CONFLATED)
        override fun toString(): String = "ConflatedChannel"
        override val isConflated: Boolean get() = true
    },
    ARRAY_BROADCAST_1 {
        override fun create(): Channel<Int> = ChannelViaBroadcast(BroadcastChannel(1))
        override fun toString(): String = "ArrayBroadcastChannel(1)"
    },
    ARRAY_BROADCAST_10 {
        override fun create(): Channel<Int> = ChannelViaBroadcast(BroadcastChannel(10))
        override fun toString(): String = "ArrayBroadcastChannel(10)"
    },
    CONFLATED_BROADCAST {
        override fun create(): Channel<Int> = ChannelViaBroadcast(ConflatedBroadcastChannel<Int>())
        override fun toString(): String = "ConflatedBroadcastChannel"
        override val isConflated: Boolean get() = true
    }
    ;

    abstract fun create(): Channel<Int>
    open val isConflated: Boolean get() = false
}

private class ChannelViaBroadcast<E>(
    private val broadcast: BroadcastChannel<E>
): Channel<E>, SendChannel<E> by broadcast {
    val sub = broadcast.openSubscription()

    override val isClosedForReceive: Boolean get() = sub.isClosedForReceive
    override val isEmpty: Boolean get() = sub.isEmpty

    override suspend fun receive(): E = sub.receive()
    override suspend fun receiveOrNull(): E? = sub.receiveOrNull()
    override fun poll(): E? = sub.poll()
    override fun iterator(): ChannelIterator<E> = sub.iterator()
    
    override fun cancel(cause: CancellationException?) = sub.cancel(cause)

    // implementing hidden method anyway, so can cast to an internal class
    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.2.0, binary compatibility with versions <= 1.1.x")
    override fun cancel(cause: Throwable?): Boolean = (sub as AbstractChannel).cancelInternal(cause)

    override val onReceive: SelectClause1<E>
        get() = sub.onReceive
    override val onReceiveOrNull: SelectClause1<E?>
        get() = sub.onReceiveOrNull
}
