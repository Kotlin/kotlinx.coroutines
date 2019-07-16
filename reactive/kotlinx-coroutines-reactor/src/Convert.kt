/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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
@ExperimentalCoroutinesApi
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
@ExperimentalCoroutinesApi
public fun <T> Deferred<T?>.asMono(context: CoroutineContext): Mono<T> = mono(context) { this@asMono.await() }

/**
 * Converts a stream of elements received from the channel to the hot reactive flux.
 *
 * Every subscriber receives values from this channel in **fan-out** fashion. If the are multiple subscribers,
 * they'll receive values in round-robin way.
 *
 * **Note: This API will become obsolete in future updates with introduction of lazy asynchronous streams.**
 *           See [issue #254](https://github.com/Kotlin/kotlinx.coroutines/issues/254).
 *
 * @param context -- the coroutine context from which the resulting flux is going to be signalled
 */
@ObsoleteCoroutinesApi
public fun <T> ReceiveChannel<T>.asFlux(context: CoroutineContext = EmptyCoroutineContext): Flux<T> = flux(context) {
    for (t in this@asFlux)
        send(t)
}