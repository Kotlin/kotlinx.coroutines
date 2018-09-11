/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.reactor

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import reactor.core.publisher.*
import kotlin.coroutines.experimental.*

/**
 * Converts this job to the hot reactive mono that signals
 * with [success][MonoSink.success] when the corresponding job completes.
 *
 * Every subscriber gets the signal at the same time.
 * Unsubscribing from the resulting mono **does not** affect the original job in any way.
 *
 * @param context -- the coroutine context from which the resulting mono is going to be signalled
 */
public fun Job.asMono(context: CoroutineContext = DefaultDispatcher): Mono<Unit> = GlobalScope.mono(context) { this@asMono.join() }

/**
 * Converts this deferred value to the hot reactive mono that signals
 * [success][MonoSink.success] or [error][MonoSink.error].
 *
 * Every subscriber gets the same completion value.
 * Unsubscribing from the resulting mono **does not** affect the original deferred value in any way.
 *
 * @param context -- the coroutine context from which the resulting mono is going to be signalled
 */
public fun <T> Deferred<T?>.asMono(context: CoroutineContext = DefaultDispatcher): Mono<T> = GlobalScope.mono(context) { this@asMono.await() }

/**
 * Converts a stream of elements received from the channel to the hot reactive flux.
 *
 * Every subscriber receives values from this channel in **fan-out** fashion. If the are multiple subscribers,
 * they'll receive values in round-robin way.
 *
 * @param context -- the coroutine context from which the resulting flux is going to be signalled
 */
public fun <T> ReceiveChannel<T>.asFlux(context: CoroutineContext = DefaultDispatcher): Flux<T> = GlobalScope.flux(context) {
    for (t in this@asFlux)
        send(t)
}