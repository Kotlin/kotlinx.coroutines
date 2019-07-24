package kotlinx.coroutines.reactor

import kotlinx.coroutines.InternalCoroutinesApi
import kotlinx.coroutines.reactive.ContextInjector
import org.reactivestreams.Publisher
import reactor.core.publisher.Flux
import reactor.core.publisher.Mono
import reactor.util.context.Context
import kotlin.coroutines.CoroutineContext

/** @suppress */
@InternalCoroutinesApi
class ReactorContextInjector : ContextInjector {
    /**
     * Injects all values from the [ReactorContext] entry of the given coroutine context
     * into the downstream [Context] of Reactor's [Publisher] instances of [Mono] or [Flux].
     */
    override fun <T> injectCoroutineContext(publisher: Publisher<T>, coroutineContext: CoroutineContext): Publisher<T> {
        val reactorContext = coroutineContext[ReactorContext]?.context ?: return publisher
        return when(publisher) {
            is Mono -> publisher.subscriberContext(reactorContext)
            is Flux -> publisher.subscriberContext(reactorContext)
            else -> publisher
        }
    }
}