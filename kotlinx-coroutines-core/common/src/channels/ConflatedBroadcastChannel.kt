/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.intrinsics.*
import kotlinx.coroutines.selects.*
import kotlin.jvm.*

/**
 * Broadcasts the most recently sent element (aka [value]) to all [openSubscription] subscribers.
 *
 * Back-to-send sent elements are _conflated_ -- only the the most recently sent value is received,
 * while previously sent elements **are lost**.
 * Every subscriber immediately receives the most recently sent element.
 * Sender to this broadcast channel never suspends and [trySend] always succeeds.
 *
 * A secondary constructor can be used to create an instance of this class that already holds a value.
 * This channel is also created by `BroadcastChannel(Channel.CONFLATED)` factory function invocation.
 *
 * This implementation is fully lock-free. In this implementation
 * [opening][openSubscription] and [closing][ReceiveChannel.cancel] subscription takes O(N) time, where N is the
 * number of subscribers.
 *
 * **Note: This API is obsolete.** It will be deprecated and replaced by [StateFlow][kotlinx.coroutines.flow.StateFlow]
 * when it becomes stable.
 */
@ExperimentalCoroutinesApi // not @ObsoleteCoroutinesApi to reduce burden for people who are still using it
public class ConflatedBroadcastChannel<E>() : BroadcastChannel<E> {
    /**
     * Creates an instance of this class that already holds a value.
     *
     * It is as a shortcut to creating an instance with a default constructor and
     * immediately sending an element: `ConflatedBroadcastChannel().apply { offer(value) }`.
     */
    public constructor(value: E) : this() {
        _state.lazySet(State<E>(value, null))
    }

    private val _state = atomic<Any>(INITIAL_STATE) // State | Closed
    private val _updating = atomic(0)
    // State transitions: null -> handler -> HANDLER_INVOKED
    private val onCloseHandler = atomic<Any?>(null)

    private companion object {
        private val CLOSED = Closed(null)
        private val UNDEFINED = Symbol("UNDEFINED")
        private val INITIAL_STATE = State<Any?>(UNDEFINED, null)
    }

    private class State<E>(
        @JvmField val value: Any?, // UNDEFINED | E
        @JvmField val subscribers: Array<Subscriber<E>>?
    )

    private class Closed(@JvmField val closeCause: Throwable?) {
        val sendException: Throwable get() = closeCause ?: ClosedSendChannelException(DEFAULT_CLOSE_MESSAGE)
        val valueException: Throwable get() = closeCause ?: IllegalStateException(DEFAULT_CLOSE_MESSAGE)
    }

    /**
     * The most recently sent element to this channel.
     *
     * Access to this property throws [IllegalStateException] when this class is constructed without
     * initial value and no value was sent yet or if it was [closed][close] without a cause.
     * It throws the original [close][SendChannel.close] cause exception if the channel has _failed_.
     */
    @Suppress("UNCHECKED_CAST")
    public val value: E get() {
        _state.loop { state ->
            when (state) {
                is Closed -> throw state.valueException
                is State<*> -> {
                    if (state.value === UNDEFINED) throw IllegalStateException("No value")
                    return state.value as E
                }
                else -> error("Invalid state $state")
            }
        }
    }

    /**
     * The most recently sent element to this channel or `null` when this class is constructed without
     * initial value and no value was sent yet or if it was [closed][close].
     */
    public val valueOrNull: E? get() = when (val state = _state.value) {
        is Closed -> null
        is State<*> -> UNDEFINED.unbox<E?>(state.value)
        else -> error("Invalid state $state")
    }

    public override val isClosedForSend: Boolean get() = _state.value is Closed

    @Suppress("UNCHECKED_CAST")
    public override fun openSubscription(): ReceiveChannel<E> {
        val subscriber = Subscriber(this)
        _state.loop { state ->
            when (state) {
                is Closed -> {
                    subscriber.close(state.closeCause)
                    return subscriber
                }
                is State<*> -> {
                    if (state.value !== UNDEFINED)
                        subscriber.offerInternal(state.value as E)
                    val update = State(state.value, addSubscriber((state as State<E>).subscribers, subscriber))
                    if (_state.compareAndSet(state, update))
                        return subscriber
                }
                else -> error("Invalid state $state")
            }
        }
    }

    @Suppress("UNCHECKED_CAST")
    private fun closeSubscriber(subscriber: Subscriber<E>) {
        _state.loop { state ->
            when (state) {
                is Closed -> return
                is State<*> -> {
                    val update = State(state.value, removeSubscriber((state as State<E>).subscribers!!, subscriber))
                    if (_state.compareAndSet(state, update))
                        return
                }
                else -> error("Invalid state $state")
            }
        }
    }

    private fun addSubscriber(list: Array<Subscriber<E>>?, subscriber: Subscriber<E>): Array<Subscriber<E>> {
        if (list == null) return Array(1) { subscriber }
        return list + subscriber
    }

    @Suppress("UNCHECKED_CAST")
    private fun removeSubscriber(list: Array<Subscriber<E>>, subscriber: Subscriber<E>): Array<Subscriber<E>>? {
        val n = list.size
        val i = list.indexOf(subscriber)
        assert { i >= 0 }
        if (n == 1) return null
        val update = arrayOfNulls<Subscriber<E>>(n - 1)
        list.copyInto(
            destination = update,
            endIndex = i
        )
        list.copyInto(
            destination = update,
            destinationOffset = i,
            startIndex = i + 1
        )
        return update as Array<Subscriber<E>>
    }

    @Suppress("UNCHECKED_CAST")
    public override fun close(cause: Throwable?): Boolean {
        _state.loop { state ->
            when (state) {
                is Closed -> return false
                is State<*> -> {
                    val update = if (cause == null) CLOSED else Closed(cause)
                    if (_state.compareAndSet(state, update)) {
                        (state as State<E>).subscribers?.forEach { it.close(cause) }
                        invokeOnCloseHandler(cause)
                        return true
                    }
                }
                else -> error("Invalid state $state")
            }
        }
    }

    private fun invokeOnCloseHandler(cause: Throwable?) {
        val handler = onCloseHandler.value
        if (handler !== null && handler !== HANDLER_INVOKED
            && onCloseHandler.compareAndSet(handler, HANDLER_INVOKED)) {
            @Suppress("UNCHECKED_CAST")
            (handler as Handler)(cause)
        }
    }

    override fun invokeOnClose(handler: Handler) {
        // Intricate dance for concurrent invokeOnClose and close
        if (!onCloseHandler.compareAndSet(null, handler)) {
            val value = onCloseHandler.value
            if (value === HANDLER_INVOKED) {
                throw IllegalStateException("Another handler was already registered and successfully invoked")
            } else {
                throw IllegalStateException("Another handler was already registered: $value")
            }
        } else {
            val state = _state.value
            if (state is Closed && onCloseHandler.compareAndSet(handler, HANDLER_INVOKED)) {
                (handler)(state.closeCause)
            }
        }
    }

    /**
     * @suppress This method has bad semantics when cause is not a [CancellationException]. Use [cancel].
     */
    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.2.0, binary compatibility with versions <= 1.1.x")
    public override fun cancel(cause: Throwable?): Boolean = close(cause)

    /**
     * Cancels this conflated broadcast channel with an optional cause, same as [close].
     * This function closes the channel with
     * the specified cause (unless it was already closed),
     * and [cancels][ReceiveChannel.cancel] all open subscriptions.
     * A cause can be used to specify an error message or to provide other details on
     * a cancellation reason for debugging purposes.
     */
    public override fun cancel(cause: CancellationException?) {
        close(cause)
    }

    /**
     * Sends the value to all subscribed receives and stores this value as the most recent state for
     * future subscribers. This implementation never suspends.
     * It throws exception if the channel [isClosedForSend] (see [close] for details).
     */
    public override suspend fun send(element: E) {
        offerInternal(element)?.let { throw it.sendException }
    }

    /**
     * Sends the value to all subscribed receives and stores this value as the most recent state for
     * future subscribers. This implementation always returns either successful result
     * or closed with an exception.
     */
    public override fun trySend(element: E): ChannelResult<Unit> {
        offerInternal(element)?.let { return ChannelResult.closed(it.sendException)  }
        return ChannelResult.success(Unit)
    }

    @Suppress("UNCHECKED_CAST")
    private fun offerInternal(element: E): Closed? {
        // If some other thread is updating the state in its offer operation we assume that our offer had linearized
        // before that offer (we lost) and that offer overwrote us and conflated our offer.
        if (!_updating.compareAndSet(0, 1)) return null
        try {
            _state.loop { state ->
                when (state) {
                    is Closed -> return state
                    is State<*> -> {
                        val update = State(element, (state as State<E>).subscribers)
                        if (_state.compareAndSet(state, update)) {
                            // Note: Using offerInternal here to ignore the case when this subscriber was
                            // already concurrently closed (assume the close had conflated our offer for this
                            // particular subscriber).
                            state.subscribers?.forEach { it.offerInternal(element) }
                            return null
                        }
                    }
                    else -> error("Invalid state $state")
                }
            }
        } finally {
            _updating.value = 0 // reset the updating flag to zero even when something goes wrong
        }
    }

    public override val onSend: SelectClause2<E, SendChannel<E>>
        get() = object : SelectClause2<E, SendChannel<E>> {
            override fun <R> registerSelectClause2(select: SelectInstance<R>, param: E, block: suspend (SendChannel<E>) -> R) {
                registerSelectSend(select, param, block)
            }
        }

    private fun <R> registerSelectSend(select: SelectInstance<R>, element: E, block: suspend (SendChannel<E>) -> R) {
        if (!select.trySelect()) return
        offerInternal(element)?.let {
            select.resumeSelectWithException(it.sendException)
            return
        }
        block.startCoroutineUnintercepted(receiver = this, completion = select.completion)
    }

    private class Subscriber<E>(
        private val broadcastChannel: ConflatedBroadcastChannel<E>
    ) : ConflatedChannel<E>(null), ReceiveChannel<E> {

        override fun onCancelIdempotent(wasClosed: Boolean) {
            if (wasClosed) {
                broadcastChannel.closeSubscriber(this)
            }
        }

        public override fun offerInternal(element: E): Any = super.offerInternal(element)
    }
}
