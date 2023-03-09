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

/**
 * Awaits the single value from the given [Mono] without blocking the thread and returns the resulting value, or, if
 * this publisher has produced an error, throws the corresponding exception. If the Mono completed without a value,
 * `null` is returned.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately cancels its [Subscription] and resumes with [CancellationException].
 */
public suspend fun <T> Mono<T>.awaitSingleOrNull(): T? = suspendCancellableCoroutine { cont ->
    injectCoroutineContext(cont.context).subscribe(object : Subscriber<T> {
        private var value: T? = null

        override fun onSubscribe(s: Subscription) {
            cont.invokeOnCancellation { s.cancel() }
            s.request(Long.MAX_VALUE)
        }

        override fun onComplete() {
            cont.resume(value)
            value = null
        }

        override fun onNext(t: T) {
            // We don't return the value immediately because the process that emitted it may not be finished yet.
            // Resuming now could lead to race conditions between emitter and the awaiting code.
            value = t
        }

        override fun onError(error: Throwable) { cont.resumeWithException(error) }
    })
}

/**
 * Awaits the single value from the given [Mono] without blocking the thread and returns the resulting value, or,
 * if this Mono has produced an error, throws the corresponding exception.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately cancels its [Subscription] and resumes with [CancellationException].
 *
 * @throws NoSuchElementException if the Mono does not emit any value
 */
// TODO: consider using https://github.com/Kotlin/kotlinx.coroutines/issues/2607 once that lands
public suspend fun <T> Mono<T>.awaitSingle(): T = awaitSingleOrNull() ?: throw NoSuchElementException()

private fun <T> monoInternal(
    scope: CoroutineScope, // support for legacy mono in scope
    context: CoroutineContext,
    block: suspend CoroutineScope.() -> T?
): Mono<T> = Mono.create { sink ->
    val reactorContext = context.extendReactorContext(sink.currentContext())
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

/**
 * @suppress
 */
@Deprecated(
    message = "CoroutineScope.mono is deprecated in favour of top-level mono",
    level = DeprecationLevel.HIDDEN,
    replaceWith = ReplaceWith("mono(context, block)")
) // Since 1.3.0, will be error in 1.3.1 and hidden in 1.4.0
public fun <T> CoroutineScope.mono(
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend CoroutineScope.() -> T?
): Mono<T> = monoInternal(this, context, block)

/**
 * This is a lint function that was added already deprecated in order to guard against confusing usages on [Mono].
 * On [Publisher] instances other than [Mono], this function is not deprecated.
 *
 * Both [awaitFirst] and [awaitSingle] await the first value, or throw [NoSuchElementException] if there is none, but
 * the name [Mono.awaitSingle] better reflects the semantics of [Mono].
 *
 * For example, consider this code:
 * ```
 * myDbClient.findById(uniqueId).awaitFirst() // findById returns a `Mono`
 * ```
 * It looks like more than one value could be returned from `findById` and [awaitFirst] discards the extra elements,
 * when in fact, at most a single value can be present.
 *
 * @suppress
 */
@Deprecated(
    message = "Mono produces at most one value, so the semantics of dropping the remaining elements are not useful. " +
        "Please use awaitSingle() instead.",
    level = DeprecationLevel.HIDDEN,
    replaceWith = ReplaceWith("this.awaitSingle()")
) // Warning since 1.5, error in 1.6
public suspend fun <T> Mono<T>.awaitFirst(): T = awaitSingle()

/**
 * This is a lint function that was added already deprecated in order to guard against confusing usages on [Mono].
 * On [Publisher] instances other than [Mono], this function is not deprecated.
 *
 * Both [awaitFirstOrDefault] and [awaitSingleOrNull] await the first value, or return some special value if there
 * is none, but the name [Mono.awaitSingleOrNull] better reflects the semantics of [Mono].
 *
 * For example, consider this code:
 * ```
 * myDbClient.findById(uniqueId).awaitFirstOrDefault(default) // findById returns a `Mono`
 * ```
 * It looks like more than one value could be returned from `findById` and [awaitFirstOrDefault] discards the extra
 * elements, when in fact, at most a single value can be present.
 *
 * @suppress
 */
@Deprecated(
    message = "Mono produces at most one value, so the semantics of dropping the remaining elements are not useful. " +
        "Please use awaitSingleOrNull() instead.",
    level = DeprecationLevel.HIDDEN,
    replaceWith = ReplaceWith("this.awaitSingleOrNull() ?: default")
) // Warning since 1.5, error in 1.6
public suspend fun <T> Mono<T>.awaitFirstOrDefault(default: T): T = awaitSingleOrNull() ?: default

/**
 * This is a lint function that was added already deprecated in order to guard against confusing usages on [Mono].
 * On [Publisher] instances other than [Mono], this function is not deprecated.
 *
 * Both [awaitFirstOrNull] and [awaitSingleOrNull] await the first value, or return some special value if there
 * is none, but the name [Mono.awaitSingleOrNull] better reflects the semantics of [Mono].
 *
 * For example, consider this code:
 * ```
 * myDbClient.findById(uniqueId).awaitFirstOrNull() // findById returns a `Mono`
 * ```
 * It looks like more than one value could be returned from `findById` and [awaitFirstOrNull] discards the extra
 * elements, when in fact, at most a single value can be present.
 *
 * @suppress
 */
@Deprecated(
    message = "Mono produces at most one value, so the semantics of dropping the remaining elements are not useful. " +
        "Please use awaitSingleOrNull() instead.",
    level = DeprecationLevel.HIDDEN,
    replaceWith = ReplaceWith("this.awaitSingleOrNull()")
) // Warning since 1.5, error in 1.6
public suspend fun <T> Mono<T>.awaitFirstOrNull(): T? = awaitSingleOrNull()

/**
 * This is a lint function that was added already deprecated in order to guard against confusing usages on [Mono].
 * On [Publisher] instances other than [Mono], this function is not deprecated.
 *
 * Both [awaitFirstOrElse] and [awaitSingleOrNull] await the first value, or return some special value if there
 * is none, but the name [Mono.awaitSingleOrNull] better reflects the semantics of [Mono].
 *
 * For example, consider this code:
 * ```
 * myDbClient.findById(uniqueId).awaitFirstOrElse(defaultValue) // findById returns a `Mono`
 * ```
 * It looks like more than one value could be returned from `findById` and [awaitFirstOrElse] discards the extra
 * elements, when in fact, at most a single value can be present.
 *
 * @suppress
 */
@Deprecated(
    message = "Mono produces at most one value, so the semantics of dropping the remaining elements are not useful. " +
        "Please use awaitSingleOrNull() instead.",
    level = DeprecationLevel.HIDDEN,
    replaceWith = ReplaceWith("this.awaitSingleOrNull() ?: defaultValue()")
) // Warning since 1.5, error in 1.6
public suspend fun <T> Mono<T>.awaitFirstOrElse(defaultValue: () -> T): T = awaitSingleOrNull() ?: defaultValue()

/**
 * This is a lint function that was added already deprecated in order to guard against confusing usages on [Mono].
 * On [Publisher] instances other than [Mono], this function is not deprecated.
 *
 * Both [awaitLast] and [awaitSingle] await the single value, or throw [NoSuchElementException] if there is none, but
 * the name [Mono.awaitSingle] better reflects the semantics of [Mono].
 *
 * For example, consider this code:
 * ```
 * myDbClient.findById(uniqueId).awaitLast() // findById returns a `Mono`
 * ```
 * It looks like more than one value could be returned from `findById` and [awaitLast] discards the initial elements,
 * when in fact, at most a single value can be present.
 *
 * @suppress
 */
@Deprecated(
    message = "Mono produces at most one value, so the last element is the same as the first. " +
        "Please use awaitSingle() instead.",
    level = DeprecationLevel.HIDDEN,
    replaceWith = ReplaceWith("this.awaitSingle()")
) // Warning since 1.5, error in 1.6
public suspend fun <T> Mono<T>.awaitLast(): T = awaitSingle()
