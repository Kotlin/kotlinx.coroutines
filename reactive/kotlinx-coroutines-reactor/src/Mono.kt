/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")

package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import kotlinx.coroutines.reactive.*
import org.reactivestreams.*
import reactor.core.*
import reactor.core.publisher.*
import kotlin.coroutines.*
import kotlin.internal.*
import kotlinx.coroutines.internal.*

/**
 * Creates a cold [mono][Mono] that runs a given [block] in a coroutine and emits its result.
 * Every time the returned mono is subscribed, it starts a new coroutine.
 * If the result of [block] is `null`, [MonoSink.success] is invoked without a value.
 * Unsubscribing cancels the running coroutine.
 *
 * Coroutine context can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 *
 * @throws IllegalArgumentException if the provided [context] contains a [Job] instance.
 */
public fun <T> mono(
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend CoroutineScope.() -> T?
): Mono<T> {
    require(context[Job] === null) { "Mono context cannot contain job in it." +
            "Its lifecycle should be managed via Disposable handle. Had $context" }
    return monoInternal(GlobalScope, context, block)
}

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
) : AbstractCoroutine<T>(parentContext, false, true), Disposable {
    @Volatile
    private var disposed = false

    override fun onCompleted(value: T) {
        if (value == null) sink.success() else sink.success(value)
    }

    override fun onCancelled(cause: Throwable, handled: Boolean) {
        /** Cancellation exceptions that were caused by [dispose], that is, came from downstream, are not errors. */
        val unwrappedCause = unwrap(cause)
        if (getCancellationException() !== unwrappedCause || !disposed) {
            try {
                /** If [sink] turns out to already be in a terminal state, this exception will be passed through the
                 * [Hooks.onOperatorError] hook, which is the way to signal undeliverable exceptions in Reactor. */
                sink.error(cause)
            } catch (e: Throwable) {
                // In case of improper error implementation or fatal exceptions
                cause.addSuppressed(e)
                handleCoroutineException(context, cause)
            }
        }
    }

    override fun dispose() {
        disposed = true
        cancel()
    }

    override fun isDisposed(): Boolean = disposed
}

@Deprecated(
    message = "CoroutineScope.mono is deprecated in favour of top-level mono",
    level = DeprecationLevel.HIDDEN,
    replaceWith = ReplaceWith("mono(context, block)")
) // Since 1.3.0, will be error in 1.3.1 and hidden in 1.4.0
public fun <T> CoroutineScope.mono(
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend CoroutineScope.() -> T?
): Mono<T> = monoInternal(this, context, block)

