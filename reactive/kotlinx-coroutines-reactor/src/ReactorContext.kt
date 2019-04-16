package kotlinx.coroutines.reactor

import kotlinx.coroutines.ExperimentalCoroutinesApi
import reactor.util.context.Context
import kotlin.coroutines.*

/**
 * Marks coroutine context element that contains Reactor's [Context] elements in [context] for seamless integration
 * between [CoroutineContext] and Reactor's [Context].
 *
 * [Context.asCoroutineContext] is defined to add Reactor's [Context] elements as part of [CoroutineContext].
 *
 * Reactor builders: [mono], [flux] can extract the reactor context from their coroutine context and
 * pass it on. Modifications of reactor context can be retrieved by `coroutineContext[ReactorContext]`.
 *
 * Example usage:
 *
 * Passing reactor context from coroutine builder to reactor entity:
 *
 * ```
 * launch(Context.of("key", "value").asCoroutineContext()) {
 *   mono {
 *     assertEquals(coroutineContext[ReactorContext]!!.context.get("key"), "value")
 *   }.subscribe()
 * }
 * ```
 *
 * Accessing modified reactor context enriched from downstream via coroutine context:
 *
 * ```
 * launch {
 *   mono {
 *     assertEquals(coroutineContext[ReactorContext]!!.context.get("key"), "value")
 *   }.subscriberContext(Context.of("key", "value"))
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
 * and later retrieved via `coroutineContext[ReactorContext]`.
 */
@ExperimentalCoroutinesApi
public fun Context.asCoroutineContext(): CoroutineContext = ReactorContext(this)