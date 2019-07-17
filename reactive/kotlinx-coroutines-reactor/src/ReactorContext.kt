package kotlinx.coroutines.reactor

import kotlinx.coroutines.ExperimentalCoroutinesApi
import reactor.util.context.Context
import kotlin.coroutines.*

/**
 * Wraps Reactor's [Context] into [CoroutineContext] element for seamless integration Reactor and kotlinx.coroutines.
 *
 * [Context.asCoroutineContext] is defined to add Reactor's [Context] elements as part of [CoroutineContext].
 *
 * Reactor builders [mono] and [flux] use this context element to enhance the resulting `subscriberContext`.
 *
 * ### Usages
 * Passing reactor context from coroutine builder to reactor entity:
 * ```
 * launch(Context.of("key", "value").asCoroutineContext()) {
 *     mono {
 *         println(coroutineContext[ReactorContext]) // Prints { "key": "value" }
 *     }.subscribe()
 * }
 * ```
 *
 * Accessing modified reactor context enriched from the downstream:
 * ```
 * launch {
 *     mono {
 *         println(coroutineContext[ReactorContext]) // Prints { "key": "value" }
 *     }.subscriberContext(Context.of("key", "value"))
 *    .subscribe()
 * }
 * ```
 */
@ExperimentalCoroutinesApi
public class ReactorContext(val context: Context) : AbstractCoroutineContextElement(ReactorContext) {
    companion object Key : CoroutineContext.Key<ReactorContext>
}

/**
 * Wraps the given [Context] into [ReactorContext], so it can be added to coroutine's context
 * and later used via `coroutineContext[ReactorContext]`.
 */
@ExperimentalCoroutinesApi
public fun Context.asCoroutineContext(): ReactorContext = ReactorContext(this)