@file:JvmName("FlowKt")

package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.flowOn
import kotlinx.coroutines.reactive.FlowSubscription
import reactor.core.CoreSubscriber
import reactor.core.publisher.Flux

/**
 * Converts the given flow to a cold flux.
 * The original flow is cancelled when the flux subscriber is disposed.
 */
@ExperimentalCoroutinesApi
public fun <T: Any> Flow<T>.asFlux(): Flux<T> = FlowAsFlux(this)

private class FlowAsFlux<T : Any>(private val flow: Flow<T>) : Flux<T>() {
    override fun subscribe(subscriber: CoreSubscriber<in T>?) {
        if (subscriber == null) throw NullPointerException()
        val hasContext = subscriber.currentContext().isEmpty
        val source = if (hasContext) flow.flowOn(subscriber.currentContext().asCoroutineContext()) else flow
        subscriber.onSubscribe(FlowSubscription(source, subscriber))
    }
}