/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactor

import kotlinx.coroutines.ExperimentalCoroutinesApi
import reactor.util.context.Context
import kotlin.coroutines.*
import kotlinx.coroutines.reactive.*

/**
 * Wraps Reactor's [Context] into [CoroutineContext] element for seamless integration Reactor and kotlinx.coroutines.
 * [Context.asCoroutineContext] is defined to add Reactor's [Context] elements as part of [CoroutineContext].
 * Coroutine context element that propagates information about Reactor's [Context] through coroutines.
 *
 * This context element is implicitly propagated through subscriber's context by all Reactive integrations, such as [mono], [flux],
 * [Publisher.asFlow][asFlow], [Flow.asPublisher][asPublisher] and [Flow.asFlux][asFlux].
 * Functions that subscribe to the reactive stream (e.g. [Publisher.awaitFirst][awaitFirst]) also propagate [ReactorContext] to the
 * subscriber's [Context].
 **
 * ### Examples of Reactive context integration.
 *
 * #### Propagating ReactorContext to Reactor's Context
 * ```
 * val flux = myDatabaseService.getUsers()
 *     .subscriberContext() { ctx -> println(ctx); ctx }
 * flux.await() // Will print "null"
 *
 * // Now add ReactorContext
 * withContext(Context.of("answer", "42").asCoroutineContext()) {
 *    flux.await() // Will print "Context{'key'='value'}"
 * }
 * ```
 *
 * #### Propagating subscriber's Context to ReactorContext:
 * ```
 * val flow = flow {
 *     println("Reactor context in Flow: " + coroutineContext[ReactorContext])
 * }
 * // No context
 * flow.asFlux()
 *     .subscribe() // Will print 'Reactor context in Flow: null'
 * // Add subscriber's context
 * flow.asFlux()
 *     .subscriberContext { ctx -> ctx.put("answer", 42) }
 *     .subscribe() // Will print "Reactor context in Flow: Context{'answer'=42}"
 * ```
 */
@ExperimentalCoroutinesApi
public class ReactorContext(public val context: Context) : AbstractCoroutineContextElement(ReactorContext) {
    public companion object Key : CoroutineContext.Key<ReactorContext>
}

/**
 * Wraps the given [Context] into [ReactorContext], so it can be added to coroutine's context
 * and later used via `coroutineContext[ReactorContext]`.
 */
@ExperimentalCoroutinesApi
public fun Context.asCoroutineContext(): ReactorContext = ReactorContext(this)
