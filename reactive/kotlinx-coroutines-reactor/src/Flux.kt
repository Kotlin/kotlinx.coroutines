/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.reactor

import kotlinx.coroutines.experimental.DefaultDispatcher
import kotlinx.coroutines.experimental.channels.ProducerScope
import kotlinx.coroutines.experimental.reactive.publish
import reactor.core.publisher.Flux
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Creates cold reactive [Flux] that runs a given [block] in a coroutine.
 * Every time the returned flux is subscribed, it starts a new coroutine in the specified [context].
 * Coroutine emits items with `send`. Unsubscribing cancels running coroutine.
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
@JvmOverloads // for binary compatibility with older code compiled before context had a default
fun <T> flux(
        context: CoroutineContext = DefaultDispatcher,
        block: suspend ProducerScope<T>.() -> Unit
): Flux<T> = Flux.from(publish(context, block = block))
