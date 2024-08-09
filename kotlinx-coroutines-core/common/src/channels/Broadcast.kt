@file:Suppress("DEPRECATION", "DEPRECATION_ERROR")

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.Channel.Factory.CONFLATED
import kotlinx.coroutines.channels.Channel.Factory.UNLIMITED
import kotlinx.coroutines.intrinsics.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

/**
 * @suppress obsolete since 1.5.0, WARNING since 1.7.0, ERROR since 1.9.0
 */
@ObsoleteCoroutinesApi
@Deprecated(level = DeprecationLevel.ERROR, message = "BroadcastChannel is deprecated in the favour of SharedFlow and is no longer supported")
public fun <E> ReceiveChannel<E>.broadcast(
    capacity: Int = 1,
    start: CoroutineStart = CoroutineStart.LAZY
): BroadcastChannel<E> {
    val scope = GlobalScope + Dispatchers.Unconfined + CoroutineExceptionHandler { _, _ -> }
    val channel = this
    // We can run this coroutine in the context that ignores all exceptions, because of `onCompletion = consume()`
    // which passes all exceptions upstream to the source ReceiveChannel
    return scope.broadcast(capacity = capacity, start = start, onCompletion = { cancelConsumed(it) }) {
        for (e in channel) {
            send(e)
        }
    }
}

/**
 * @suppress obsolete since 1.5.0, WARNING since 1.7.0, ERROR since 1.9.0
 */
@ObsoleteCoroutinesApi
@Deprecated(level = DeprecationLevel.ERROR, message = "BroadcastChannel is deprecated in the favour of SharedFlow and is no longer supported")
public fun <E> CoroutineScope.broadcast(
    context: CoroutineContext = EmptyCoroutineContext,
    capacity: Int = 1,
    start: CoroutineStart = CoroutineStart.LAZY,
    onCompletion: CompletionHandler? = null,
    @BuilderInference block: suspend ProducerScope<E>.() -> Unit
): BroadcastChannel<E> {
    val newContext = newCoroutineContext(context)
    val channel = BroadcastChannel<E>(capacity)
    val coroutine = if (start.isLazy)
        LazyBroadcastCoroutine(newContext, channel, block) else
        BroadcastCoroutine(newContext, channel, active = true)
    if (onCompletion != null) coroutine.invokeOnCompletion(handler = onCompletion)
    coroutine.start(start, coroutine, block)
    return coroutine
}

private open class BroadcastCoroutine<E>(
    parentContext: CoroutineContext,
    protected val _channel: BroadcastChannel<E>,
    active: Boolean
) : AbstractCoroutine<Unit>(parentContext, initParentJob = false, active = active),
    ProducerScope<E>, BroadcastChannel<E> by _channel {

    init {
        initParentJob(parentContext[Job])
    }

    override val isActive: Boolean get() = super.isActive

    override val channel: SendChannel<E>
        get() = this

    @Suppress("MULTIPLE_DEFAULTS_INHERITED_FROM_SUPERTYPES_DEPRECATION_WARNING") // do not remove the MULTIPLE_DEFAULTS suppression: required in K2
    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.2.0, binary compatibility with versions <= 1.1.x")
    final override fun cancel(cause: Throwable?): Boolean {
        cancelInternal(cause ?: defaultCancellationException())
        return true
    }

    @Suppress("MULTIPLE_DEFAULTS_INHERITED_FROM_SUPERTYPES_DEPRECATION_WARNING") // do not remove the MULTIPLE_DEFAULTS suppression: required in K2
    final override fun cancel(cause: CancellationException?) {
        cancelInternal(cause ?: defaultCancellationException())
    }

    override fun cancelInternal(cause: Throwable) {
        val exception = cause.toCancellationException()
        _channel.cancel(exception) // cancel the channel
        cancelCoroutine(exception) // cancel the job
    }

    override fun onCompleted(value: Unit) {
        _channel.close()
    }

    override fun onCancelled(cause: Throwable, handled: Boolean) {
        val processed = _channel.close(cause)
        if (!processed && !handled) handleCoroutineException(context, cause)
    }

    // The BroadcastChannel could be also closed
    override fun close(cause: Throwable?): Boolean {
        val result = _channel.close(cause)
        start() // start coroutine if it was not started yet
        return result
    }
}

private class LazyBroadcastCoroutine<E>(
    parentContext: CoroutineContext,
    channel: BroadcastChannel<E>,
    block: suspend ProducerScope<E>.() -> Unit
) : BroadcastCoroutine<E>(parentContext, channel, active = false) {
    private val continuation = block.createCoroutineUnintercepted(this, this)

    override fun openSubscription(): ReceiveChannel<E> {
        // open subscription _first_
        val subscription = _channel.openSubscription()
        // then start coroutine
        start()
        return subscription
    }

    override fun onStart() {
        continuation.startCoroutineCancellable(this)
    }
}
