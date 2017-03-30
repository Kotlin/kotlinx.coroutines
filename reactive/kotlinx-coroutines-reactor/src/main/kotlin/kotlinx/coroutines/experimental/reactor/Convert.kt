package kotlinx.coroutines.experimental.reactor

import kotlinx.coroutines.experimental.Deferred
import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.channels.ReceiveChannel
import reactor.core.publisher.Flux
import reactor.core.publisher.Mono
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Converts this job to the hot reactive mono that signals
 * with [success][MonoSink.success] when the corresponding job completes.
 *
 * Every subscriber gets the signal at the same time.
 * Unsubscribing from the resulting mono **does not** affect the original job in any way.
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
 * @param context -- the coroutine context from which the resulting mono is going to be signalled
 */
public fun <T> Deferred<T?>.asMono(context: CoroutineContext): Mono<T> = mono(context) { this@asMono.await() }

/**
 * Converts a stream of elements received from the channel to the hot reactive flux.
 *
 * Every subscriber receives values from this channel in **fan-out** fashion. If the are multiple subscribers,
 * they'll receive values in round-robin way.
 *
 * @param context -- the coroutine context from which the resulting flux is going to be signalled
 */
public fun <T> ReceiveChannel<T>.asFlux(context: CoroutineContext): Flux<T> = flux(context) {
    for (t in this@asFlux)
        send(t)
}