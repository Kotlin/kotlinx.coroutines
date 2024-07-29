@file:Suppress("FunctionName", "DEPRECATION", "DEPRECATION_ERROR")

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.BufferOverflow.*
import kotlinx.coroutines.channels.Channel.Factory.BUFFERED
import kotlinx.coroutines.channels.Channel.Factory.CHANNEL_DEFAULT_CAPACITY
import kotlinx.coroutines.channels.Channel.Factory.CONFLATED
import kotlinx.coroutines.channels.Channel.Factory.UNLIMITED
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*

/**
 * @suppress obsolete since 1.5.0, WARNING since 1.7.0, ERROR since 1.9.0
 */
@ObsoleteCoroutinesApi
@Deprecated(level = DeprecationLevel.ERROR, message = "BroadcastChannel is deprecated in the favour of SharedFlow and is no longer supported")
public interface BroadcastChannel<E> : SendChannel<E> {
    /**
     * @suppress
     */
    public fun openSubscription(): ReceiveChannel<E>

    /**
     * @suppress
     */
    public fun cancel(cause: CancellationException? = null)

    /**
     * @suppress
     */
    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Binary compatibility only")
    public fun cancel(cause: Throwable? = null): Boolean
}

/**
 * @suppress obsolete since 1.5.0, WARNING since 1.7.0, ERROR since 1.9.0
 */
@ObsoleteCoroutinesApi
@Deprecated(level = DeprecationLevel.ERROR, message = "BroadcastChannel is deprecated in the favour of SharedFlow and StateFlow, and is no longer supported")
public fun <E> BroadcastChannel(capacity: Int): BroadcastChannel<E> =
    when (capacity) {
        0 -> throw IllegalArgumentException("Unsupported 0 capacity for BroadcastChannel")
        UNLIMITED -> throw IllegalArgumentException("Unsupported UNLIMITED capacity for BroadcastChannel")
        CONFLATED -> ConflatedBroadcastChannel()
        BUFFERED -> BroadcastChannelImpl(CHANNEL_DEFAULT_CAPACITY)
        else -> BroadcastChannelImpl(capacity)
    }

/**
 * @suppress obsolete since 1.5.0, WARNING since 1.7.0, ERROR since 1.9.0
 */
@ObsoleteCoroutinesApi
@Deprecated(level = DeprecationLevel.ERROR, message = "ConflatedBroadcastChannel is deprecated in the favour of SharedFlow and is no longer supported")
public class ConflatedBroadcastChannel<E> private constructor(
    private val broadcast: BroadcastChannelImpl<E>
) : BroadcastChannel<E> by broadcast {
    public constructor(): this(BroadcastChannelImpl<E>(capacity = CONFLATED))
    /**
     * @suppress
     */
    public constructor(value: E) : this() {
        trySend(value)
    }

    /**
     * @suppress
     */
    public val value: E get() = broadcast.value

    /**
     * @suppress
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
@Suppress("MULTIPLE_DEFAULTS_INHERITED_FROM_SUPERTYPES_DEPRECATION_WARNING", "MULTIPLE_DEFAULTS_INHERITED_FROM_SUPERTYPES_WHEN_NO_EXPLICIT_OVERRIDE_DEPRECATION_WARNING") // do not remove the MULTIPLE_DEFAULTS suppression: required in K2
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
