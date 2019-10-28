/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")

package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import reactor.core.*
import reactor.core.publisher.*
import kotlin.coroutines.*
import kotlin.internal.*

/**
 * Creates cold [mono][Mono] that will run a given [block] in a coroutine.
 * Every time the returned mono is subscribed, it starts a new coroutine.
 * Coroutine returns a single, possibly null value. Unsubscribing cancels running coroutine.
 *
 * | **Coroutine action**                  | **Signal to sink**
 * | ------------------------------------- | ------------------------
 * | Returns a non-null value              | `success(value)`
 * | Returns a null                        | `success`
 * | Failure with exception or unsubscribe | `error`
 *
 * Coroutine context can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 *
 * Method throws [IllegalArgumentException] if provided [context] contains a [Job] instance.
 */
public fun <T> mono(
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend CoroutineScope.() -> T?
): Mono<T> {
    require(context[Job] === null) { "Mono context cannot contain job in it." +
            "Its lifecycle should be managed via Disposable handle. Had $context" }
    return monoInternal(GlobalScope, context, block)
}

@Deprecated(
    message = "CoroutineScope.mono is deprecated in favour of top-level mono",
    level = DeprecationLevel.ERROR,
    replaceWith = ReplaceWith("mono(context, block)")
) // Since 1.3.0, will be error in 1.3.1 and hidden in 1.4.0
@LowPriorityInOverloadResolution
public fun <T> CoroutineScope.mono(
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend CoroutineScope.() -> T?
): Mono<T> = monoInternal(this, context, block)

private fun <T> monoInternal(
    scope: CoroutineScope, // support for legacy mono in scope
    context: CoroutineContext,
    block: suspend CoroutineScope.() -> T?
): Mono<T> = Mono.create { sink ->
    val reactorContext = (context[ReactorContext]?.context?.putAll(sink.currentContext()) ?: sink.currentContext()).asCoroutineContext()
    val newContext = scope.newCoroutineContext(context + reactorContext)
    val coroutine = MonoCoroutine(newContext, sink)
    sink.onDispose(coroutine)
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
}

private class MonoCoroutine<in T>(
    parentContext: CoroutineContext,
    private val sink: MonoSink<T>
) : AbstractCoroutine<T>(parentContext, true), Disposable {
    var disposed = false

    override fun onCompleted(value: T) {
        if (!disposed) {
            if (value == null) sink.success() else sink.success(value)
        }
    }

    override fun onCancelled(cause: Throwable, handled: Boolean) {
        if (!disposed) {
            sink.error(cause)
        } else if (!handled) {
            handleCoroutineException(context, cause)
        }
    }

    override fun dispose() {
        disposed = true
        cancel()
    }

    override fun isDisposed(): Boolean = disposed
}
