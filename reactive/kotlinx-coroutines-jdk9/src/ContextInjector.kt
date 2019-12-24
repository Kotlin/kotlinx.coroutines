package kotlinx.coroutines.jdk9

import kotlinx.coroutines.InternalCoroutinesApi
import java.util.concurrent.Flow.Publisher
import kotlin.coroutines.CoroutineContext

/** @suppress */
@InternalCoroutinesApi
public interface ContextInjector {
    /**
     * Injects `ReactorContext` element from the given context into the `SubscriberContext` of the publisher.
     * This API used as an indirection layer between `reactive` and `reactor` modules.
     */
    public fun <T> injectCoroutineContext(publisher: Publisher<T>, coroutineContext: CoroutineContext): Publisher<T>
}