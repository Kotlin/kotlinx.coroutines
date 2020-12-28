/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

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
            is Mono -> publisher.contextWrite(reactorContext)
            is Flux -> publisher.contextWrite(reactorContext)
            else -> publisher
        }
    }
}
