package kotlinx.coroutines.reactor

import kotlinx.coroutines.reactive.*
import org.reactivestreams.*
import reactor.core.publisher.*
import reactor.util.context.*
import kotlin.coroutines.*

internal class ReactorContextInjector : ContextInjector {
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