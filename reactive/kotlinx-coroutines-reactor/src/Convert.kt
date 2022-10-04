/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import reactor.core.publisher.*
import kotlin.coroutines.*

/**
 * Converts this job to the hot reactive mono that signals
 * with [success][MonoSink.success] when the corresponding job completes.
 *
 * Every subscriber gets the signal at the same time.
 * Unsubscribing from the resulting mono **does not** affect the original job in any way.
 *
 * **Note: This is an experimental api.** Conversion of coroutines primitives to reactive entities may change
 *    in the future to account for the concept of structured concurrency.
 *
 * @param context -- the coroutine context from which the resulting mono is going to be signalled
 */
public fun Job.asMono(context: CoroutineContext): Mono<Unit> = mono(context) { this@asMono.join() }
/**
 * Converts this deferred value to the hot reactive mono that signals
 * [success][MonoSink.success] or [error][MonoSink.error].
 *
 * Every subscriber gets the same completion value.
 * Unsubscribing from the resulting mono **does not** affect the original deferred value in any way.
 *
 * **Note: This is an experimental api.** Conversion of coroutines primitives to reactive entities may change
 *    in the future to account for the concept of structured concurrency.
 *
 * @param context -- the coroutine context from which the resulting mono is going to be signalled
 */
public fun <T> Deferred<T?>.asMono(context: CoroutineContext): Mono<T> = mono(context) { this@asMono.await() }

/**
 * Converts a stream of elements received from the channel to the hot reactive flux.
 *
 * Every subscriber receives values from this channel in a **fan-out** fashion. If the are multiple subscribers,
 * they'll receive values in a round-robin way.
 * @param context -- the coroutine context from which the resulting flux is going to be signalled
 * @suppress
 */
@Deprecated(message = "Deprecated in the favour of consumeAsFlow()",
    level = DeprecationLevel.ERROR,
    replaceWith = ReplaceWith("this.consumeAsFlow().asFlux(context)", imports = ["kotlinx.coroutines.flow.consumeAsFlow"]))
public fun <T> ReceiveChannel<T>.asFlux(context: CoroutineContext = EmptyCoroutineContext): Flux<T> = flux(context) {
    for (t in this@asFlux)
        send(t)
}
