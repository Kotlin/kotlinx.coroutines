/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("FunctionName", "DEPRECATION")

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.BufferOverflow.*
import kotlinx.coroutines.channels.Channel.Factory.BUFFERED
import kotlinx.coroutines.channels.Channel.Factory.CHANNEL_DEFAULT_CAPACITY
import kotlinx.coroutines.channels.Channel.Factory.CONFLATED
import kotlinx.coroutines.channels.Channel.Factory.UNLIMITED
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*
import kotlin.native.concurrent.*

/**
 * Broadcast channel is a non-blocking primitive for communication between the sender and multiple receivers
 * that subscribe for the elements using [openSubscription] function and unsubscribe using [ReceiveChannel.cancel]
 * function.
 *
 * See `BroadcastChannel()` factory function for the description of available
 * broadcast channel implementations.
 *
 * **Note: This API is obsolete since 1.5.0 and deprecated for removal since 1.7.0**
 * It is replaced with [SharedFlow][kotlinx.coroutines.flow.SharedFlow].
 */
@ObsoleteCoroutinesApi
@Deprecated(level = DeprecationLevel.WARNING, message = "BroadcastChannel is deprecated in the favour of SharedFlow and is no longer supported")
public interface BroadcastChannel<E> : SendChannel<E> {
    /**
     * Subscribes to this [BroadcastChannel] and returns a channel to receive elements from it.
     * The resulting channel shall be [cancelled][ReceiveChannel.cancel] to unsubscribe from this
     * broadcast channel.
     */
    public fun openSubscription(): ReceiveChannel<E>

    /**
     * Cancels reception of remaining elements from this channel with an optional cause.
     * This function closes the channel with
     * the specified cause (unless it was already closed), removes all buffered sent elements from it,
     * and [cancels][ReceiveChannel.cancel] all open subscriptions.
     * A cause can be used to specify an error message or to provide other details on
     * a cancellation reason for debugging purposes.
     */
    public fun cancel(cause: CancellationException? = null)

    /**
     * @suppress This method has bad semantics when cause is not a [CancellationException]. Use [cancel].
     */
    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Binary compatibility only")
    public fun cancel(cause: Throwable? = null): Boolean
}

/**
 * Creates a broadcast channel with the specified buffer capacity.
 *
 * The resulting channel type depends on the specified [capacity] parameter:
 *
 * * when `capacity` positive, but less than [UNLIMITED] -- creates `ArrayBroadcastChannel` with a buffer of given capacity.
 *   **Note:** this channel looses all items that have been sent to it until the first subscriber appears;
 * * when `capacity` is [CONFLATED] -- creates [ConflatedBroadcastChannel] that conflates back-to-back sends;
 * * when `capacity` is [BUFFERED] -- creates `ArrayBroadcastChannel` with a default capacity.
 * * otherwise -- throws [IllegalArgumentException].
 *
 * **Note: This API is obsolete since 1.5.0 and deprecated for removal since 1.7.0**
 * It is replaced with [SharedFlow][kotlinx.coroutines.flow.SharedFlow] and [StateFlow][kotlinx.coroutines.flow.StateFlow].
 */
@ObsoleteCoroutinesApi
@Deprecated(level = DeprecationLevel.WARNING, message = "BroadcastChannel is deprecated in the favour of SharedFlow and StateFlow, and is no longer supported")
public fun <E> BroadcastChannel(capacity: Int): BroadcastChannel<E> =
    when (capacity) {
        0 -> throw IllegalArgumentException("Unsupported 0 capacity for BroadcastChannel")
        UNLIMITED -> throw IllegalArgumentException("Unsupported UNLIMITED capacity for BroadcastChannel")
        CONFLATED -> ConflatedBroadcastChannel()
        BUFFERED -> BroadcastChannelImpl(CHANNEL_DEFAULT_CAPACITY)
        else -> BroadcastChannelImpl(capacity)
    }

/**
 * Broadcasts the most recently sent element (aka [value]) to all [openSubscription] subscribers.
 *
 * Back-to-send sent elements are _conflated_ -- only the most recently sent value is received,
 * while previously sent elements **are lost**.
 * Every subscriber immediately receives the most recently sent element.
 * Sender to this broadcast channel never suspends and [trySend] always succeeds.
 *
 * A secondary constructor can be used to create an instance of this class that already holds a value.
 * This channel is also created by `BroadcastChannel(Channel.CONFLATED)` factory function invocation.
 *
 * In this implementation, [opening][openSubscription] and [closing][ReceiveChannel.cancel] subscription
 * takes linear time in the number of subscribers.
 *
 * **Note: This API is obsolete since 1.5.0 and deprecated for removal since 1.7.0**
 * It is replaced with [SharedFlow][kotlinx.coroutines.flow.StateFlow].
 */
@ObsoleteCoroutinesApi
@Deprecated(level = DeprecationLevel.WARNING, message = "ConflatedBroadcastChannel is deprecated in the favour of SharedFlow and is no longer supported")
public class ConflatedBroadcastChannel<E> private constructor(
    private val broadcast: BroadcastChannelImpl<E>
) : BroadcastChannel<E> by broadcast {
    public constructor(): this(BroadcastChannelImpl<E>(capacity = CONFLATED))
    /**
     * Creates an instance of this class that already holds a value.
     *
     * It is as a shortcut to creating an instance with a default constructor and
     * immediately sending an element: `ConflatedBroadcastChannel().apply { offer(value) }`.
     */
    public constructor(value: E) : this() {
        trySend(value)
    }

    /**
     * The most recently sent element to this channel.
     *
     * Access to this property throws [IllegalStateException] when this class is constructed without
     * initial value and no value was sent yet or if it was [closed][close] without a cause.
     * It throws the original [close][SendChannel.close] cause exception if the channel has _failed_.
     */
    public val value: E get() = broadcast.value
    /**
     * The most recently sent element to this channel or `null` when this class is constructed without
     * initial value and no value was sent yet or if it was [closed][close].
     */
    public val valueOrNull: E? get() = broadcast.valueOrNull
}

/**
 * A common implementation for both the broadcast channel with a buffer of fixed [capacity]
 * and the conflated broadcast channel (see [ConflatedBroadcastChannel]).
 *
 * **Note**, that elements that are sent to this channel while there are no
 * [openSubscription] subscribers are immediately lost.
 *
 * This channel is created by `BroadcastChannel(capacity)` factory function invocation.
 */
internal class BroadcastChannelImpl<E>(
    /**
     * Buffer capacity; [Channel.CONFLATED] when this broadcast is conflated.
     */
    val capacity: Int
) : BufferedChannel<E>(capacity = Channel.RENDEZVOUS, onUndeliveredElement = null), BroadcastChannel<E> {
    init {
        require(capacity >= 1 || capacity == CONFLATED) {
            "BroadcastChannel capacity must be positive or Channel.CONFLATED, but $capacity was specified"
        }
    }

    // This implementation uses coarse-grained synchronization,
    // as, reputedly, it is the simplest synchronization scheme.
    // All operations are protected by this lock.
    private val lock = ReentrantLock()
    // The list of subscribers; all accesses should be protected by lock.
    // Each change must create a new list instance to avoid `ConcurrentModificationException`.
    private var subscribers: List<BufferedChannel<E>> = emptyList()
    // When this broadcast is conflated, this field stores the last sent element.
    // If this channel is empty or not conflated, it stores a special `NO_ELEMENT` marker.
    private var lastConflatedElement: Any? = NO_ELEMENT // NO_ELEMENT or E

    // ###########################
    // # Subscription Management #
    // ###########################

    override fun openSubscription(): ReceiveChannel<E> = lock.withLock { // protected by lock
        // Is this broadcast conflated or buffered?
        // Create the corresponding subscription channel.
        val s = if (capacity == CONFLATED) SubscriberConflated() else SubscriberBuffered()
        // If this broadcast is already closed or cancelled,
        // and the last sent element is not available in case
        // this broadcast is conflated, close the created
        // subscriber immediately and return it.
        if (isClosedForSend && lastConflatedElement === NO_ELEMENT) {
            s.close(closeCause)
            return s
        }
        // Is this broadcast conflated? If so, send
        // the last sent element to the subscriber.
        if (lastConflatedElement !== NO_ELEMENT) {
            s.trySend(value)
        }
        // Add the subscriber to the list and return it.
        subscribers += s
        s
    }

    private fun removeSubscriber(s: ReceiveChannel<E>) = lock.withLock { // protected by lock
        subscribers = subscribers.filter { it !== s }
    }

    // #############################
    // # The `send(..)` Operations #
    // #############################

    /**
     * Sends the specified element to all subscribers.
     *
     * **!!! THIS IMPLEMENTATION IS NOT LINEARIZABLE !!!**
     *
     * As the operation should send the element to multiple
     * subscribers simultaneously, it is non-trivial to
     * implement it in an atomic way. Specifically, this
     * would require a special implementation that does
     * not transfer the element until all parties are able
     * to resume it (this `send(..)` can be cancelled
     * or the broadcast can become closed in the meantime).
     * As broadcasts are obsolete, we keep this implementation
     * as simple as possible, allowing non-linearizability
     * in corner cases.
     */
    override suspend fun send(element: E) {
        val subs = lock.withLock { // protected by lock
            // Is this channel closed for send?
            if (isClosedForSend) throw sendException
            // Update the last sent element if this broadcast is conflated.
            if (capacity == CONFLATED) lastConflatedElement = element
            // Get a reference to the list of subscribers under the lock.
            subscribers
        }
        // The lock has been released. Send the element to the
        // subscribers one-by-one, and finish immediately
        // when this broadcast discovered in the closed state.
        // Note that this implementation is non-linearizable;
        // see this method documentation for details.
        subs.forEach {
            // We use special function to send the element,
            // which returns `true` on success and `false`
            // if the subscriber is closed.
            val success = it.sendBroadcast(element)
            // The sending attempt has failed.
            // Check whether the broadcast is closed.
            if (!success && isClosedForSend) throw sendException
        }
    }

    override fun trySend(element: E): ChannelResult<Unit> = lock.withLock { // protected by lock
        // Is this channel closed for send?
        if (isClosedForSend) return super.trySend(element)
        // Check whether the plain `send(..)` operation
        // should suspend and fail in this case.
        val shouldSuspend = subscribers.any { it.shouldSendSuspend() }
        if (shouldSuspend) return ChannelResult.failure()
        // Update the last sent element if this broadcast is conflated.
        if (capacity == CONFLATED) lastConflatedElement = element
        // Send the element to all subscribers.
        // It is guaranteed that the attempt cannot fail,
        // as both the broadcast closing and subscription
        // cancellation are guarded by lock, which is held
        // by the current operation.
        subscribers.forEach { it.trySend(element) }
        // Finish with success.
        return ChannelResult.success(Unit)
    }

    // ###########################################
    // # The `select` Expression: onSend { ... } #
    // ###########################################

    override fun registerSelectForSend(select: SelectInstance<*>, element: Any?) {
        // It is extremely complicated to support sending via `select` for broadcasts,
        // as the operation should wait on multiple subscribers simultaneously.
        // At the same time, broadcasts are obsolete, so we need a simple implementation
        // that works somehow. Here is a tricky work-around. First, we launch a new
        // coroutine that performs plain `send(..)` operation and tries to complete
        // this `select` via `trySelect`, independently on whether it is in the
        // registration or in the waiting phase. On success, the operation finishes.
        // On failure, if another clause is already selected or the `select` operation
        // has been cancelled, we observe non-linearizable behaviour, as this `onSend`
        // clause is completed as well. However, we believe that such a non-linearizability
        // is fine for obsolete API. The last case is when the `select` operation is still
        // in the registration case, so this `onSend` clause should be re-registered.
        // The idea is that we keep information that this `onSend` clause is already selected
        // and finish immediately.
        @Suppress("UNCHECKED_CAST")
        element as E
        // First, check whether this `onSend` clause is already
        // selected, finishing immediately in this case.
        lock.withLock {
            val result = onSendInternalResult.remove(select)
            if (result != null) { // already selected!
                // `result` is either `Unit` ot `CHANNEL_CLOSED`.
                select.selectInRegistrationPhase(result)
                return
            }
        }
        // Start a new coroutine that performs plain `send(..)`
        // and tries to select this `onSend` clause at the end.
        CoroutineScope(select.context).launch(start = CoroutineStart.UNDISPATCHED) {
            val success: Boolean = try {
                send(element)
                // The element has been successfully sent!
                true
            } catch (t: Throwable) {
                // This broadcast must be closed. However, it is possible that
                // an unrelated exception, such as `OutOfMemoryError` has been thrown.
                // This implementation checks that the channel is actually closed,
                // re-throwing the caught exception otherwise.
                if (isClosedForSend && (t is ClosedSendChannelException || sendException === t)) false
                else throw t
            }
            // Mark this `onSend` clause as selected and
            // try to complete the `select` operation.
            lock.withLock {
                // Status of this `onSend` clause should not be presented yet.
                assert { onSendInternalResult[select] == null }
                // Success or fail? Put the corresponding result.
                onSendInternalResult[select] = if (success) Unit else CHANNEL_CLOSED
                // Try to select this `onSend` clause.
                select as SelectImplementation<*>
                val trySelectResult = select.trySelectDetailed(this@BroadcastChannelImpl,  Unit)
                if (trySelectResult !== TrySelectDetailedResult.REREGISTER) {
                    // In case of re-registration (this `select` was still
                    // in the registration phase), the algorithm will invoke
                    // `registerSelectForSend`. As we stored an information that
                    // this `onSend` clause is already selected (in `onSendInternalResult`),
                    // the algorithm, will complete immediately. Otherwise, to avoid memory
                    // leaks, we must remove this information from the hashmap.
                    onSendInternalResult.remove(select)
                }
            }

        }
    }
    private val onSendInternalResult = HashMap<SelectInstance<*>, Any?>() // select -> Unit or CHANNEL_CLOSED

    // ############################
    // # Closing and Cancellation #
    // ############################

    override fun close(cause: Throwable?): Boolean = lock.withLock { // protected by lock
        // Close all subscriptions first.
        subscribers.forEach { it.close(cause) }
        // Remove all subscriptions that do not contain
        // buffered elements or waiting send-s to avoid
        // memory leaks. We must keep other subscriptions
        // in case `broadcast.cancel(..)` is called.
        subscribers = subscribers.filter { it.hasElements() }
        // Delegate to the parent implementation.
        super.close(cause)
    }

    override fun cancelImpl(cause: Throwable?): Boolean = lock.withLock { // protected by lock
        // Cancel all subscriptions. As part of cancellation procedure,
        // subscriptions automatically remove themselves from this broadcast.
        subscribers.forEach { it.cancelImpl(cause) }
        // For the conflated implementation, clear the last sent element.
        lastConflatedElement = NO_ELEMENT
        // Finally, delegate to the parent implementation.
        super.cancelImpl(cause)
    }

    override val isClosedForSend: Boolean
        // Protect by lock to synchronize with `close(..)` / `cancel(..)`.
        get() = lock.withLock { super.isClosedForSend }

    // ##############################
    // # Subscriber Implementations #
    // ##############################

    private inner class SubscriberBuffered : BufferedChannel<E>(capacity = capacity) {
        public override fun cancelImpl(cause: Throwable?): Boolean = lock.withLock {
            // Remove this subscriber from the broadcast on cancellation.
            removeSubscriber(this@SubscriberBuffered )
            super.cancelImpl(cause)
        }
    }

    private inner class SubscriberConflated : ConflatedBufferedChannel<E>(capacity = 1, onBufferOverflow = DROP_OLDEST) {
        public override fun cancelImpl(cause: Throwable?): Boolean {
            // Remove this subscriber from the broadcast on cancellation.
            removeSubscriber(this@SubscriberConflated )
            return super.cancelImpl(cause)
        }
    }

    // ########################################
    // # ConflatedBroadcastChannel Operations #
    // ########################################

    @Suppress("UNCHECKED_CAST")
    val value: E get() = lock.withLock {
        // Is this channel closed for sending?
        if (isClosedForSend) {
            throw closeCause ?: IllegalStateException("This broadcast channel is closed")
        }
        // Is there sent element?
        if (lastConflatedElement === NO_ELEMENT) error("No value")
        // Return the last sent element.
        lastConflatedElement as E
    }

    @Suppress("UNCHECKED_CAST")
    val valueOrNull: E? get() = lock.withLock {
        // Is this channel closed for sending?
        if (isClosedForReceive) null
        // Is there sent element?
        else if (lastConflatedElement === NO_ELEMENT) null
        // Return the last sent element.
        else lastConflatedElement as E
    }

    // #################
    // # For Debugging #
    // #################

    override fun toString() =
        (if (lastConflatedElement !== NO_ELEMENT) "CONFLATED_ELEMENT=$lastConflatedElement; " else "") +
            "BROADCAST=<${super.toString()}>; " +
            "SUBSCRIBERS=${subscribers.joinToString(separator = ";", prefix = "<", postfix = ">")}"
}

private val NO_ELEMENT = Symbol("NO_ELEMENT")
