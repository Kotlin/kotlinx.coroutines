/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.selects.*

enum class TestChannelKind {
    RENDEZVOUS {
        override fun create(): Channel<Int> = RendezvousChannel()
        override fun toString(): String = "RendezvousChannel"
    },
    ARRAY_1 {
        override fun create(): Channel<Int> = ArrayChannel(1)
        override fun toString(): String = "ArrayChannel(1)"
    },
    ARRAY_10 {
        override fun create(): Channel<Int> = ArrayChannel(10)
        override fun toString(): String = "ArrayChannel(10)"
    },
    LINKED_LIST {
        override fun create(): Channel<Int> = LinkedListChannel()
        override fun toString(): String = "LinkedListChannel"
    },
    CONFLATED {
        override fun create(): Channel<Int> = ConflatedChannel()
        override fun toString(): String = "ConflatedChannel"
        override val isConflated: Boolean get() = true
    },
    ARRAY_BROADCAST_1 {
        override fun create(): Channel<Int> = ChannelViaBroadcast(ArrayBroadcastChannel<Int>(1))
        override fun toString(): String = "ArrayBroadcastChannel(1)"
    },
    ARRAY_BROADCAST_10 {
        override fun create(): Channel<Int> = ChannelViaBroadcast(ArrayBroadcastChannel<Int>(10))
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
    override fun cancel(): Boolean = sub.cancel()
    override fun cancel(cause: Throwable?): Boolean = sub.cancel(cause)
    override val onReceive: SelectClause1<E>
        get() = sub.onReceive
    override val onReceiveOrNull: SelectClause1<E?>
        get() = sub.onReceiveOrNull
}
