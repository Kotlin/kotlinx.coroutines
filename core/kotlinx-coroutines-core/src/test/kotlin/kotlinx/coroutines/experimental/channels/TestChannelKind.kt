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

import kotlinx.coroutines.experimental.selects.SelectClause1

enum class TestChannelKind {
    RENDEZVOUS {
        override fun create(): Channel<Int> = RendezvousChannel<Int>()
        override fun toString(): String = "RendezvousChannel"
    },
    ARRAY_1 {
        override fun create(): Channel<Int> = ArrayChannel<Int>(1)
        override fun toString(): String = "ArrayChannel(1)"
    },
    ARRAY_10 {
        override fun create(): Channel<Int> = ArrayChannel<Int>(8)
        override fun toString(): String = "ArrayChannel(8)"
    },
    LINKED_LIST {
        override fun create(): Channel<Int> = LinkedListChannel<Int>()
        override fun toString(): String = "LinkedListChannel"
    },
    CONFLATED {
        override fun create(): Channel<Int> = ConflatedChannel<Int>()
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
    suspend override fun receive(): E = sub.receive()
    suspend override fun receiveOrNull(): E? = sub.receiveOrNull()
    override fun poll(): E? = sub.poll()
    override fun iterator(): ChannelIterator<E> = sub.iterator()
    override fun cancel(cause: Throwable?): Boolean = sub.cancel(cause)
    override val onReceive: SelectClause1<E>
        get() = sub.onReceive
    override val onReceiveOrNull: SelectClause1<E?>
        get() = sub.onReceiveOrNull
}
