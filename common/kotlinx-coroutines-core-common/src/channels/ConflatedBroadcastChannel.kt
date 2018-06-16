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

import kotlinx.atomicfu.*
import kotlinx.coroutines.experimental.internal.*
import kotlinx.coroutines.experimental.intrinsics.*
import kotlinx.coroutines.experimental.selects.*
import kotlinx.coroutines.experimental.internal.ReentrantLock
import kotlinx.coroutines.experimental.internal.Symbol
import kotlinx.coroutines.experimental.internal.subscriberList
import kotlinx.coroutines.experimental.internal.withLock
import kotlinx.coroutines.experimental.internalAnnotations.JvmField
import kotlinx.coroutines.experimental.internalAnnotations.Volatile
import kotlinx.coroutines.experimental.intrinsics.startCoroutineUndispatched
import kotlinx.coroutines.experimental.selects.SelectClause2
import kotlinx.coroutines.experimental.selects.SelectInstance

/**
 * Broadcasts the most recently sent element (aka [value]) to all [openSubscription] subscribers.
 *
 * Back-to-send sent elements are _conflated_ -- only the the most recently sent value is received,
 * while previously sent elements **are lost**.
 * Every subscriber immediately receives the most recently sent element.
 * Sender to this broadcast channel never suspends and [offer] always returns `true`.
 *
 * A secondary constructor can be used to create an instance of this class that already holds a value.
 * This channel is also created by `BroadcastChannel(Channel.CONFLATED)` factory function invocation.
 *
 * This implementation is synchronized. In this implementation
 * [opening][openSubscription] and [closing][ReceiveChannel.cancel] subscription takes O(N) time, where N is the
 * number of subscribers.
 */
public class ConflatedBroadcastChannel<E>() : BroadcastChannel<E> {

    public constructor(value: E) : this() {
        _state = value
    }

    private val _lock = ReentrantLock()

    @Volatile
    private var _state: Any? = UNDEFINED

    private val _subscribers = subscriberList<Subscriber>()

    private val _onCloseHandlers = subscriberList<Handler>()

    /**
     * The most recently sent element to this channel.
     *
     * Access to this property throws [IllegalStateException] when this class is constructed without
     * initial value and no value was sent yet or if it was [closed][close] without a cause.
     * It throws the original [close][SendChannel.close] cause exception if the channel has _failed_.
     */
    @Suppress("UNCHECKED_CAST")
    public val value: E
        get() {
            val state = _state
            if (state === UNDEFINED) throw IllegalStateException("No value")
            (state as? Closed)?.run { throw valueException }
            return state as E
        }

    /**
     * The most recently sent element to this channel or `null` when this class is constructed without
     * initial value and no value was sent yet or if it was [closed][close].
     */
    @Suppress("UNCHECKED_CAST")
    public val valueOrNull: E?
        get() {
            val state = _state
            return when {
                state === UNDEFINED -> null
                state is Closed -> state.closeCause?.let { throw it }
                else -> state as E
            }
        }

    public override val isFull: Boolean get() = false

    public override val isClosedForSend: Boolean get() = _state is Closed

    public override val onSend: SelectClause2<E, SendChannel<E>>
        get() = object : SelectClause2<E, SendChannel<E>> {
            override fun <R> registerSelectClause2(select: SelectInstance<R>, param: E, block: suspend (SendChannel<E>) -> R) {
                if (!select.trySelect(null)) return
                offerInternal(param)?.let {
                    select.resumeSelectCancellableWithException(it.sendException)
                    return
                }
                block.startCoroutineUnintercepted(receiver = this@ConflatedBroadcastChannel, completion = select.completion)
            }
        }

    public override fun cancel(cause: Throwable?): Boolean = close(cause)

    public override fun close(cause: Throwable?): Boolean {
        _lock.withLock {
            if (_state is Closed) return false
            _state = Closed(cause)

            // dispose all subscribers
            _subscribers.forEach { it.close(cause) }
            _subscribers.clear()

            _onCloseHandlers.forEach { it.invoke(cause) }
            _onCloseHandlers.clear()

            return true
        }
    }

    public override fun offer(element: E): Boolean {
        offerInternal(element)?.let { throw it.sendException }
        return true
    }

    private fun offerInternal(element: E): Closed? {
        if (_lock.tryLock()) {
            try {
                (_state as? Closed)?.let { return it }

                _state = element
                _subscribers.forEach { it.tryOffer(element) }
                return null
            } finally {
                _lock.unlock()
            }
        } else {
            return _state as? Closed
        }
    }

    public override fun openSubscription(): ReceiveChannel<E> {
        val subscriber = Subscriber()
        _subscribers.add(subscriber)

        do {
            val state = _state
            @Suppress("UNCHECKED_CAST")
            when {
                state is Closed -> subscriber.close(state.closeCause)
                state !== UNDEFINED -> subscriber.tryOffer(state as E)
            }
            // manage offerInternal/close contention
        } while (_state !== state)

        if (subscriber.isClosedForSend) _subscribers.remove(subscriber)
        return subscriber
    }

    public override suspend fun send(element: E) {
        offerInternal(element)?.run { throw sendException }
    }

    override fun invokeOnClose(handler: Handler) {
        _lock.withLock {
            val state = _state
            if (state is Closed) {
                handler(state.closeCause)
            } else {
                _onCloseHandlers += handler
            }
        }
    }

    private inner class Subscriber : ConflatedChannel<E>() {

        /**
         * Offer an element without throw exception
         */
        fun tryOffer(element: E) {
            super.offerInternal(element)
        }
    }

    override fun cancel(cause: Throwable?): Boolean =
            super.cancel(cause).also { closed ->
                if (closed) this@ConflatedBroadcastChannel._subscribers.remove(this)
            }
}

private class Closed(@JvmField val closeCause: Throwable?) {
    val sendException: Throwable get() = closeCause ?: ClosedSendChannelException(DEFAULT_CLOSE_MESSAGE)
    val valueException: Throwable get() = closeCause ?: IllegalStateException(DEFAULT_CLOSE_MESSAGE)
}

private companion object {
    @JvmField
    val UNDEFINED = Symbol("UNDEFINED")
}
}
