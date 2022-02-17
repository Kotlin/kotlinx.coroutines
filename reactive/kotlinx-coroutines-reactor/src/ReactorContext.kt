/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactor

import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlin.coroutines.*
import kotlinx.coroutines.reactive.*
import reactor.util.context.*

/**
 * Wraps Reactor's [Context] into a [CoroutineContext] element for seamless integration between
 * Reactor and kotlinx.coroutines.
 * [Context.asCoroutineContext] puts Reactor's [Context] elements into a [CoroutineContext],
 * which can be used to propagate the information about Reactor's [Context] through coroutines.
 *
 * This context element is implicitly propagated through subscribers' context by all Reactive integrations,
 * such as [mono], [flux], [Publisher.asFlow][asFlow], [Flow.asPublisher][asPublisher] and [Flow.asFlux][asFlux].
 * Functions that subscribe to a reactive stream
 * (e.g. [Publisher.awaitFirst][kotlinx.coroutines.reactive.awaitFirst]), too, propagate [ReactorContext]
 * to the subscriber's [Context].
 **
 * ### Examples of Reactive context integration.
 *
 * #### Propagating ReactorContext to Reactor's Context
 * ```
 * val flux = myDatabaseService.getUsers()
 *     .contextWrite { ctx -> println(ctx); ctx }
 * flux.awaitFirst() // Will print "null"
 *
 * // Now add ReactorContext
 * withContext(Context.of("answer", "42").asCoroutineContext()) {
 *    flux.awaitFirst() // Will print "Context{'key'='value'}"
 * }
 * ```
 *
 * #### Propagating subscriber's Context to ReactorContext:
 * ```
 * val flow = flow {
 *     println("Reactor context in Flow: " + currentCoroutineContext()[ReactorContext])
 * }
 * // No context
 * flow.asFlux()
 *     .subscribe() // Will print 'Reactor context in Flow: null'
 * // Add subscriber's context
 * flow.asFlux()
 *     .contextWrite { ctx -> ctx.put("answer", 42) }
 *     .subscribe() // Will print "Reactor context in Flow: Context{'answer'=42}"
 * ```
 */
public class ReactorContext(public val context: Context) : AbstractCoroutineContextElement(ReactorContext) {

    // `Context.of` is zero-cost if the argument is a `Context`
    public constructor(contextView: ContextView): this(Context.of(contextView))

    public companion object Key : CoroutineContext.Key<ReactorContext>

    override fun toString(): String = context.toString()
}

/**
 * Wraps the given [ContextView] into [ReactorContext], so it can be added to the coroutine's context
 * and later used via `coroutineContext[ReactorContext]`.
 */
public fun ContextView.asCoroutineContext(): ReactorContext = ReactorContext(this)

/**
 * Wraps the given [Context] into [ReactorContext], so it can be added to the coroutine's context
 * and later used via `coroutineContext[ReactorContext]`.
 * @suppress
 */
@Deprecated("The more general version for ContextView should be used instead", level = DeprecationLevel.HIDDEN)
public fun Context.asCoroutineContext(): ReactorContext = readOnly().asCoroutineContext() // `readOnly()` is zero-cost.

/**
 * Updates the Reactor context in this [CoroutineContext], adding (or possibly replacing) some values.
 */
internal fun CoroutineContext.extendReactorContext(extensions: ContextView): CoroutineContext =
    (this[ReactorContext]?.context?.putAll(extensions) ?: extensions).asCoroutineContext()
