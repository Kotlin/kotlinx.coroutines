package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlinx.coroutines.flow.*

/**
 * Scope for the [produce][CoroutineScope.produce], [callbackFlow] and [channelFlow] builders.
 */
public interface ProducerScope<in E> : CoroutineScope, SendChannel<E> {
    /**
     * A reference to the channel this coroutine [sends][send] elements to.
     * It is provided for convenience, so that the code in the coroutine can refer
     * to the channel as `channel` as opposed to `this`.
     * All the [SendChannel] functions on this interface delegate to
     * the channel instance returned by this property.
     */
    public val channel: SendChannel<E>
}

/**
 * Suspends the current coroutine until the channel is either
 * [closed][SendChannel.close] or [cancelled][ReceiveChannel.cancel].
 *
 * The given [block] will be executed unconditionally before this function returns.
 * `awaitClose { cleanup() }` is a convenient shorthand for the often useful form
 * `try { awaitClose() } finally { cleanup() }`.
 *
 * This function can only be invoked directly inside the same coroutine that is its receiver.
 * Specifying the receiver of [awaitClose] explicitly is most probably a mistake.
 *
 * This suspending function is cancellable: if the [Job] of the current coroutine is [cancelled][CoroutineScope.cancel]
 * while this suspending function is waiting, this function immediately resumes with [CancellationException].
 * There is a **prompt cancellation guarantee**: even if this function is ready to return, but was cancelled
 * while suspended, [CancellationException] will be thrown. See [suspendCancellableCoroutine] for low-level details.
 *
 * Example of usage:
 * ```
 * val callbackEventsStream = produce {
 *     val disposable = registerChannelInCallback(channel)
 *     awaitClose { disposable.dispose() }
 * }
 * ```
 *
 * Internally, [awaitClose] is implemented using [SendChannel.invokeOnClose].
 * Currently, every channel can have at most one [SendChannel.invokeOnClose] handler.
 * This means that calling [awaitClose] several times in a row or combining it with other [SendChannel.invokeOnClose]
 * invocations is prohibited.
 * An [IllegalStateException] will be thrown if this rule is broken.
 *
 * **Pitfall**: when used in [produce], if the channel is [cancelled][ReceiveChannel.cancel], [awaitClose] can either
 * return normally or throw a [CancellationException] due to a race condition.
 * The reason is that, for [produce], cancelling the channel and cancelling the coroutine of the [ProducerScope] is
 * done simultaneously.
 *
 * @throws IllegalStateException if invoked from outside the [ProducerScope] (by leaking `this` outside the producer
 * coroutine).
 * @throws IllegalStateException if this channel already has a [SendChannel.invokeOnClose] handler registered.
 */
public suspend fun ProducerScope<*>.awaitClose(block: () -> Unit = {}) {
    check(kotlin.coroutines.coroutineContext[Job] === this) { "awaitClose() can only be invoked from the producer context" }
    try {
        suspendCancellableCoroutine<Unit> { cont ->
            invokeOnClose {
                cont.resume(Unit)
            }
        }
    } finally {
        block()
    }
}

/**
 * Launches a new coroutine to produce a stream of values by sending them to a channel
 * and returns a reference to the coroutine as a [ReceiveChannel]. This resulting
 * object can be used to [receive][ReceiveChannel.receive] elements produced by this coroutine.
 *
 * The scope of the coroutine contains the [ProducerScope] interface, which implements
 * both [CoroutineScope] and [SendChannel], so that the coroutine can invoke [send][SendChannel.send] directly.
 * The channel is [closed][SendChannel.close] when the coroutine completes.
 * The running coroutine is cancelled when the channel is [cancelled][ReceiveChannel.cancel].
 * When the coroutine is cancelled, however, the channel does not automatically close until the coroutine completes,
 * so it is possible to keep sending elements while handling coroutine cancellation.
 *
 * The coroutine context is inherited from this [CoroutineScope]. Additional context elements can be specified with the [context] argument.
 * If the context does not have any dispatcher or other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * The parent job is inherited from the [CoroutineScope] as well, but it can also be overridden
 * with a corresponding [context] element.
 *
 * If this coroutine finishes with an exception, it will close the channel with that exception as the cause and
 * the resulting channel will become _failed_, so that any attempt to receive from it thereafter will throw an exception.
 *
 * The kind of the resulting channel depends on the specified [capacity] parameter.
 * See the [Channel] interface documentation for details.
 *
 * See [newCoroutineContext] for a description of debugging facilities available for newly created coroutines.
 *
 * **Note: This is an experimental api.** Behaviour of producers that work as children in a parent scope with respect
 *        to cancellation and error handling may change in the future.
 *
 * @param context additional to [CoroutineScope.coroutineContext] context of the coroutine.
 * @param capacity capacity of the channel's buffer (no buffer by default).
 * @param block the coroutine code.
 */
@ExperimentalCoroutinesApi
public fun <E> CoroutineScope.produce(
    context: CoroutineContext = EmptyCoroutineContext,
    capacity: Int = Channel.RENDEZVOUS,
    @BuilderInference block: suspend ProducerScope<E>.() -> Unit
): ReceiveChannel<E> =
    produce(context, capacity, BufferOverflow.SUSPEND, CoroutineStart.DEFAULT, onCompletion = null, block = block)

/**
 * **This is an internal API and should not be used from general code.**
 * The `onCompletion` parameter will be redesigned.
 * If you have to use the `onCompletion` operator, please report to https://github.com/Kotlin/kotlinx.coroutines/issues/.
 * As a temporary solution, [invokeOnCompletion][Job.invokeOnCompletion] can be used instead:
 * ```
 * fun <E> ReceiveChannel<E>.myOperator(): ReceiveChannel<E> = GlobalScope.produce(Dispatchers.Unconfined) {
 *     coroutineContext[Job]?.invokeOnCompletion { consumes() }
 * }
 * ```
 * @suppress
 */
@InternalCoroutinesApi
public fun <E> CoroutineScope.produce(
    context: CoroutineContext = EmptyCoroutineContext,
    capacity: Int = 0,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    onCompletion: CompletionHandler? = null,
    @BuilderInference block: suspend ProducerScope<E>.() -> Unit
): ReceiveChannel<E> =
    produce(context, capacity, BufferOverflow.SUSPEND, start, onCompletion, block)

// Internal version of produce that is maximally flexible, but is not exposed through public API (too many params)
internal fun <E> CoroutineScope.produce(
    context: CoroutineContext = EmptyCoroutineContext,
    capacity: Int = 0,
    onBufferOverflow: BufferOverflow = BufferOverflow.SUSPEND,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    onCompletion: CompletionHandler? = null,
    @BuilderInference block: suspend ProducerScope<E>.() -> Unit
): ReceiveChannel<E> {
    val channel = Channel<E>(capacity, onBufferOverflow)
    val newContext = newCoroutineContext(context)
    val coroutine = ProducerCoroutine(newContext, channel)
    if (onCompletion != null) coroutine.invokeOnCompletion(handler = onCompletion)
    coroutine.start(start, coroutine, block)
    return coroutine
}

private class ProducerCoroutine<E>(
    parentContext: CoroutineContext, channel: Channel<E>
) : ChannelCoroutine<E>(parentContext, channel, true, active = true), ProducerScope<E> {
    override val isActive: Boolean
        get() = super.isActive

    override fun onCompleted(value: Unit) {
        _channel.close()
    }

    override fun onCancelled(cause: Throwable, handled: Boolean) {
        val processed = _channel.close(cause)
        if (!processed && !handled) handleCoroutineException(context, cause)
    }
}
