/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.reactive.*
import org.reactivestreams.*
import reactor.core.*
import reactor.core.publisher.*
import reactor.util.context.*
import kotlin.coroutines.*

/**
 * Creates a cold reactive [Flux] that runs the given [block] in a coroutine.
 * Every time the returned flux is subscribed, it starts a new coroutine in the specified [context].
 * The coroutine emits ([Subscriber.onNext]) values with [send][ProducerScope.send], completes ([Subscriber.onComplete])
 * when the coroutine completes, or, in case the coroutine throws an exception or the channel is closed,
 * emits the error ([Subscriber.onError]) and closes the channel with the cause.
 * Unsubscribing cancels the running coroutine.
 *
 * Invocations of [send][ProducerScope.send] are suspended appropriately when subscribers apply back-pressure and to
 * ensure that [onNext][Subscriber.onNext] is not invoked concurrently.
 *
 * **Note: This is an experimental api.** Behaviour of publishers that work as children in a parent scope with respect
 *        to cancellation and error handling may change in the future.
 *
 * @throws IllegalArgumentException if the provided [context] contains a [Job] instance.
 */
public fun <T> flux(
    context: CoroutineContext = EmptyCoroutineContext,
    @BuilderInference block: suspend ProducerScope<T>.() -> Unit
): Flux<T> {
    require(context[Job] === null) { "Flux context cannot contain job in it." +
        "Its lifecycle should be managed via Disposable handle. Had $context" }
    return Flux.from(reactorPublish(GlobalScope, context, block))
}

private fun <T> reactorPublish(
    scope: CoroutineScope,
    context: CoroutineContext = EmptyCoroutineContext,
    @BuilderInference block: suspend ProducerScope<T>.() -> Unit
): Publisher<T> = Publisher onSubscribe@{ subscriber: Subscriber<in T>? ->
    if (subscriber !is CoreSubscriber) {
        subscriber.reject(IllegalArgumentException("Subscriber is not an instance of CoreSubscriber, context can not be extracted."))
        return@onSubscribe
    }
    val currentContext = subscriber.currentContext()
    val reactorContext = context.extendReactorContext(currentContext)
    val newContext = scope.newCoroutineContext(context + reactorContext)
    val coroutine = PublisherCoroutine(newContext, subscriber, REACTOR_HANDLER)
    subscriber.onSubscribe(coroutine) // do it first (before starting coroutine), to avoid unnecessary suspensions
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
}

private val REACTOR_HANDLER: (Throwable, CoroutineContext) -> Unit = { cause, ctx ->
    if (cause !is CancellationException) {
        try {
            Operators.onOperatorError(cause, ctx[ReactorContext]?.context ?: Context.empty())
        } catch (e: Throwable) {
            cause.addSuppressed(e)
            handleCoroutineException(ctx, cause)
        }
    }
}

/** The proper way to reject the subscriber, according to
 * [the reactive spec](https://github.com/reactive-streams/reactive-streams-jvm/blob/v1.0.3/README.md#1.9)
 */
private fun <T> Subscriber<T>?.reject(t: Throwable) {
    if (this == null)
        throw NullPointerException("The subscriber can not be null")
    onSubscribe(object: Subscription {
        override fun request(n: Long) {
            // intentionally left blank
        }
        override fun cancel() {
            // intentionally left blank
        }
    })
    onError(t)
}

@Deprecated(
    message = "CoroutineScope.flux is deprecated in favour of top-level flux",
    level = DeprecationLevel.HIDDEN,
    replaceWith = ReplaceWith("flux(context, block)")
) // Since 1.3.0, will be error in 1.3.1 and hidden in 1.4.0. Binary compatibility with Spring
public fun <T> CoroutineScope.flux(
    context: CoroutineContext = EmptyCoroutineContext,
    @BuilderInference block: suspend ProducerScope<T>.() -> Unit
): Flux<T> =
    Flux.from(reactorPublish(this, context, block))
