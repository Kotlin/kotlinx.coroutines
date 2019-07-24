package kotlinx.coroutines.reactive

import kotlinx.coroutines.InternalCoroutinesApi
import org.reactivestreams.Publisher
import kotlin.coroutines.CoroutineContext

/** @suppress */
@InternalCoroutinesApi
public interface ContextInjector {
    /**
     * Injects the coroutine context into the context of the publisher.
     */
    public fun <T> injectCoroutineContext(publisher: Publisher<T>, coroutineContext: CoroutineContext): Publisher<T>
}