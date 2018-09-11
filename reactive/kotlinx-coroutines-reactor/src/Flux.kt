/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.reactor

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlinx.coroutines.experimental.reactive.*
import reactor.core.publisher.*
import kotlin.coroutines.experimental.*

/**
 * Creates cold reactive [Flux] that runs a given [block] in a coroutine.
 * Every time the returned flux is subscribed, it starts a new coroutine in the specified [context].
 * Coroutine emits items with `send`. Unsubscribing cancels running coroutine.
 *
 * Coroutine context is inherited from a [CoroutineScope], additional context elements can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * The parent job is inherited from a [CoroutineScope] as well, but it can also be overridden
 * with corresponding [coroutineContext] element.
 *
 * Invocations of `send` are suspended appropriately when subscribers apply back-pressure and to ensure that
 * `onNext` is not invoked concurrently.
 *
 * | **Coroutine action**                         | **Signal to subscriber**
 * | -------------------------------------------- | ------------------------
 * | `send`                                       | `onNext`
 * | Normal completion or `close` without cause   | `onComplete`
 * | Failure with exception or `close` with cause | `onError`
 */
fun <T> CoroutineScope.flux(
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend ProducerScope<T>.() -> Unit
): Flux<T> =
    Flux.from(publish(newCoroutineContext(context), block = block))


/**
 * Creates cold reactive [Flux] that runs a given [block] in a coroutine.
 * @suppress **Deprecated** Use [CoroutineScope.mono] instead.
 */
@Deprecated(
    message = "Standalone coroutine builders are deprecated, use extensions on CoroutineScope instead",
    replaceWith = ReplaceWith(
        "GlobalScope.flux(context, block)",
        imports = ["kotlinx.coroutines.experimental.GlobalScope", "kotlinx.coroutines.experimental.reactor.flux"]
    )
)
@JvmOverloads // for binary compatibility with older code compiled before context had a default
fun <T> flux(
    context: CoroutineContext = Dispatchers.Default,
    block: suspend ProducerScope<T>.() -> Unit
): Flux<T> =
    GlobalScope.flux(context, block)
