/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.coroutines.*

/**
 * Scope for [produce][CoroutineScope.produce] coroutine builder.
 *
 * **Note: This is an experimental api.** Behaviour of producers that work as children in a parent scope with respect
 *        to cancellation and error handling may change in the future.
 */
@ExperimentalCoroutinesApi
public interface ProducerScope<in E> : CoroutineScope, SendChannel<E> {
    /**
     * A reference to the channel that this coroutine [sends][send] elements to.
     * It is provided for convenience, so that the code in the coroutine can refer
     * to the channel as `channel` as apposed to `this`.
     * All the [SendChannel] functions on this interface delegate to
     * the channel instance returned by this function.
     */
    val channel: SendChannel<E>
}

/**
 * Suspends the current coroutine until the channel is either [closed][SendChannel.close] or [cancelled][ReceiveChannel.cancel]
 * and invokes the given [block] before resuming the coroutine.
 *
 * Note that when producer channel is cancelled this function resumes with cancellation exception,
 * so putting the code after calling this function would not lead to its execution in case of cancellation.
 * That is why this code takes a lambda parameter.
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
    check(kotlin.coroutines.coroutineContext[Job] === this) { "awaitClose() can be invoke only from the producer context" }
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
 * Launches new coroutine to produce a stream of values by sending them to a channel
 * and returns a reference to the coroutine as a [ReceiveChannel]. This resulting
 * object can be used to [receive][ReceiveChannel.receive] elements produced by this coroutine.
 *
 * The scope of the coroutine contains [ProducerScope] interface, which implements
 * both [CoroutineScope] and [SendChannel], so that coroutine can invoke
 * [send][SendChannel.send] directly. The channel is [closed][SendChannel.close]
 * when the coroutine completes.
 * The running coroutine is cancelled when its receive channel is [cancelled][ReceiveChannel.cancel].
 *
 * Coroutine context is inherited from a [CoroutineScope], additional context elements can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * The parent job is inherited from a [CoroutineScope] as well, but it can also be overridden
 * with corresponding [coroutineContext] element.
 *
 * Uncaught exceptions in this coroutine close the channel with this exception as a cause and
 * the resulting channel becomes _failed_, so that any attempt to receive from such a channel throws exception.
 *
 * The kind of the resulting channel depends on the specified [capacity] parameter.
 * See [Channel] interface documentation for details.
 *
 * See [newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
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
): ReceiveChannel<E> {
    val channel = Channel<E>(capacity)
    val newContext = newCoroutineContext(context)
    val coroutine = ProducerCoroutine(newContext, channel)
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
    return coroutine
}

/**
 * This an internal API and should not be used from general code.**
 * onCompletion parameter will be redesigned.
 * If you have to use `onCompletion` operator, please report to https://github.com/Kotlin/kotlinx.coroutines/issues/.
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
    onCompletion: CompletionHandler? = null,
    @BuilderInference block: suspend ProducerScope<E>.() -> Unit
): ReceiveChannel<E> {
    val channel = Channel<E>(capacity)
    val newContext = newCoroutineContext(context)
    val coroutine = ProducerCoroutine(newContext, channel)
    if (onCompletion != null) coroutine.invokeOnCompletion(handler = onCompletion)
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
    return coroutine
}

private class ProducerCoroutine<E>(
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
