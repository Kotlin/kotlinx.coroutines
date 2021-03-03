/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.coroutines.*

/**
 * Scope for the [produce][CoroutineScope.produce] coroutine builder.
 *
 * **Note: This is an experimental api.** Behavior of producers that work as children in a parent scope with respect
 *        to cancellation and error handling may change in the future.
 */
@ExperimentalCoroutinesApi
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
 * Suspends the current coroutine until the channel is either [closed][SendChannel.close] or [cancelled][ReceiveChannel.cancel]
 * and invokes the given [block] before resuming the coroutine.
 *
 * This suspending function is cancellable.
 * There is a **prompt cancellation guarantee**. If the job was cancelled while this function was
 * suspended, it will not resume successfully. See [suspendCancellableCoroutine] documentation for low-level details.
 *
 * Note that when the producer channel is cancelled, this function resumes with a cancellation exception.
 * Therefore, in case of cancellation, no code after the call to this function will be executed.
 * That's why this function takes a lambda parameter.
 *
 * Example of usage:
 * ```
 * val callbackEventsStream = produce {
 *     val disposable = registerChannelInCallback(channel)
 *     awaitClose { disposable.dispose() }
 * }
 * ```
 */
@ExperimentalCoroutinesApi
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
 * both [CoroutineScope] and [SendChannel], so that the coroutine can invoke
 * [send][SendChannel.send] directly. The channel is [closed][SendChannel.close]
 * when the coroutine completes.
 * The running coroutine is cancelled when its receive channel is [cancelled][ReceiveChannel.cancel].
 *
 * The coroutine context is inherited from this [CoroutineScope]. Additional context elements can be specified with the [context] argument.
 * If the context does not have any dispatcher or other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * The parent job is inherited from the [CoroutineScope] as well, but it can also be overridden
 * with a corresponding [context] element.
 *
 * Any uncaught exception in this coroutine will close the channel with this exception as the cause and
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
    capacity: Int = 0,
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

internal open class ProducerCoroutine<E>(
    parentContext: CoroutineContext, channel: Channel<E>
) : ChannelCoroutine<E>(parentContext, channel, active = true), ProducerScope<E> {
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
