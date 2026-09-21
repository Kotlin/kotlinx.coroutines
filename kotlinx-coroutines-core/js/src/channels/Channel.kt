@file:OptIn(ExperimentalJsExport::class, ExperimentalStdlibApi::class)
@file:Suppress("EXPOSED_FUNCTION_RETURN_TYPE", "INVISIBLE_REFERENCE")
package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.JsAsyncIterableIterator
import kotlinx.coroutines.internal.JsAsyncIterator
import kotlinx.coroutines.internal.JsIteratorResult
import kotlinx.coroutines.internal.recoverStackTrace
import kotlinx.coroutines.selects.*
import kotlin.internal.*
import kotlin.js.Promise

@JsImplicitExport(couldBeConvertedToExplicitExport = true)
public actual interface ReceiveChannel<out E> {
    @DelicateCoroutinesApi
    public actual val isClosedForReceive: Boolean
    @ExperimentalCoroutinesApi
    public actual val isEmpty: Boolean

    public actual fun cancel(cause: CancellationException?)

    /**
     * The version of `asyncIterator()` callable from JS.
     *
     * Exported instead of the usual `asyncIterator()` to avoid exposing the [Boolean] parameter,
     * which is non-idiomatic on JS.
     *
     * @suppress
     */
    @ExperimentalCoroutinesApi
    @JsSymbol("asyncIterator")
    // the deprecation message must be empty, or the API will be exported as deprecated to JS
    @Deprecated(message = "", level = DeprecationLevel.HIDDEN)
    public fun asyncIterator(): JsAsyncIterableIterator<E> =
        asyncIterator(cancelOnEarlyExit = true)

    /**
     * The version of `asyncIterator()` callable from JS.
     *
     * Introduced for consistency with the `.values` function of
     * [`ReadableStream`](https://developer.mozilla.org/en-US/docs/Web/API/ReadableStream).
     *
     * @param options iteration behavior options:
     * - `preventCancel = true`: early iterator completion (for example, via `break`) does not cancel the channel;
     * - `preventCancel = false` or omitted: early iterator completion cancels the channel.
     *
     * @suppress
     */
    @JsName("values") // We use "values" here to mimic the ReadableStream API: https://developer.mozilla.org/en-US/docs/Web/API/ReadableStream
    // the deprecation message must be empty, or the API will be exported as deprecated to JS
    @Deprecated(message = "", level = DeprecationLevel.HIDDEN)
    @Suppress("DEPRECATION_ERROR")
    public fun asyncIterator(options: ChannelIteratorOptions? = null): JsAsyncIterableIterator<E> =
        asyncIterator(options?.preventCancel != true)

    /**
     * Returns a JavaScript [`AsyncIterator`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/AsyncIterator)
     * for this channel.
     *
     * This method is used to implement the JavaScript async-iteration protocol](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Iteration_protocols#the_async_iterator_and_async_iterable_protocols),
     * to support iterating over the channel's elements with `for await ... of`.
     *
     * By default, the channel is [consumed][ReceiveChannel.consume] by this function.
     * Cancelling the iterator also causes the [cancellation][ReceiveChannel.cancel] of the channel.
     * [cancelOnEarlyExit] can be set to `false` to disable this behavior.
     *
     * ## Implementation details
     *
     * Each call to the iterator's `next` method receives at most one element from this channel:
     *
     * - if an element is available, the returned `Promise` is fulfilled with an iterator result
     *   whose `value` is the received element and whose `done` is `false`;
     * - if the channel is closed normally without a cause, the returned `Promise` is fulfilled
     *   with an iterator result whose `done` is `true`;
     * - if the channel is closed with a cause, the returned `Promise` is rejected with that cause.
     *
     * Calling the iterator's `return` method finishes this iterator instance and returns a fulfilled
     * `Promise` with `done` set to `true`. By default, it [cancels][ReceiveChannel.cancel] the channel without a `cause`.
     *
     * Calling the iterator's `throw` method finishes this iterator instance and returns a rejected
     * `Promise` with the supplied error. By default, it [cancels][ReceiveChannel.cancel] the channel
     * with the `cause` of the [CancellationException] being set to the exception provided to `throw`.
     *
     * The coroutines backing calls to `next` are started in [GlobalScope].
     * In particular, they are not children of any caller-provided coroutine
     * scope and therefore are not bound to the lifetime of any structured-concurrency scope.
     */
    @JsExport.Ignore
    @ExperimentalCoroutinesApi
    @OptIn(ExperimentalWasmJsInterop::class)
    public fun asyncIterator(cancelOnEarlyExit: Boolean = true): JsAsyncIterableIterator<E> {
        var wasEarlyFinished = false
        val iterator = JsAsyncIterator(
            next = {
                GlobalScope.promise {
                    if (wasEarlyFinished) return@promise JsIteratorResult(done = true)
                    val result = receiveCatching()
                    result.exceptionOrNull()?.let { throw it }
                    if (result.isClosed) {
                        JsIteratorResult(done = true)
                    } else {
                        JsIteratorResult(value = result.getOrThrow(), done = false)
                    }
                }
            },
            // Those lambdas declare a parameter, but they still work when JS call them with no arguments.
            // In JavaScript, missing arguments are assigned `undefined`, so `value` becomes `undefined`.
            // This matches the iterator protocol, where `return(value)` accepts zero or one argument.
            // https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Functions/Default_parameters#description
            _return = { value: E? ->
                wasEarlyFinished = true
                if (cancelOnEarlyExit) cancel()
                Promise.resolve(JsIteratorResult(value = value, done = true))
            },
            _throw = { err: dynamic ->
                wasEarlyFinished = true
                val cause = err.unsafeCast<JsPromiseError>().toThrowableOrNull()
                if (cancelOnEarlyExit) {
                    /** Adapted from [ReceiveChannel.cancelConsumed] */
                    cancel(cause?.let {
                        it as? CancellationException ?: CancellationException("Channel was closed via AsyncIterator#throw method", it)
                    })
                }
                Promise.reject(err)
            }
        )
        iterator.asDynamic()[js("Symbol.asyncIterator")] = { iterator }
        return iterator.unsafeCast<JsAsyncIterableIterator<E>>()
    }

    @JsExport.Ignore // Is replaced by AsyncIterable implementation
    public actual operator fun iterator(): ChannelIterator<E>

    @JsExport.Ignore // Can't be exported until the compiler supports exporting of value classes
    public actual fun tryReceive(): ChannelResult<E>

    @JsExport.Ignore // Exporting a suspend function by JsImplicitExport is a bit broken till 2.5.0
    public actual suspend fun receive(): E

    @JsExport.Ignore // Can't be exported until the compiler supports exporting of value classes
    public actual suspend fun receiveCatching(): ChannelResult<E>

    @JsExport.Ignore // Is not so easy to use on the JavaScript side, because it's implemented with the contextual operator invoke
    public actual val onReceive: SelectClause1<E>

    @JsExport.Ignore // Is not so easy to use on the JavaScript side, because it's implemented with the contextual operator invoke
    public actual val onReceiveCatching: SelectClause1<ChannelResult<E>>

    @JsExport.Ignore
    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.2.0, binary compatibility with versions <= 1.1.x")
    public actual fun cancel(cause: Throwable?): Boolean

    @JsExport.Ignore
    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.2.0, binary compatibility with versions <= 1.1.x")
    public actual fun cancel(): Unit = cancel(null)

    @JsExport.Ignore
    @Deprecated(
        level = DeprecationLevel.ERROR,
        message = "Deprecated in the favour of 'tryReceive'. " +
            "Please note that the provided replacement does not rethrow channel's close cause as 'poll' did, " +
            "for the precise replacement please refer to the 'poll' documentation",
        replaceWith = ReplaceWith("tryReceive().getOrNull()")
    ) // Warning since 1.5.0, error since 1.6.0, not hidden until 1.8+ because API is quite widespread
    public actual fun poll(): E? {
        val result = tryReceive()
        if (result.isSuccess) return result.getOrThrow()
        throw recoverStackTrace(result.exceptionOrNull() ?: return null)
    }

    @JsExport.Ignore
    @Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")
    @LowPriorityInOverloadResolution
    @Deprecated(
        message = "Deprecated in favor of 'receiveCatching'. " +
            "Please note that the provided replacement does not rethrow channel's close cause as 'receiveOrNull' did, " +
            "for the detailed replacement please refer to the 'receiveOrNull' documentation",
        level = DeprecationLevel.ERROR,
        replaceWith = ReplaceWith("receiveCatching().getOrNull()")
    ) // Warning since 1.3.0, error in 1.5.0, cannot be hidden due to deprecated extensions
    public actual suspend fun receiveOrNull(): E? = receiveCatching().getOrNull()

    @Suppress("DEPRECATION_ERROR")
    @Deprecated(
        message = "Deprecated in favor of onReceiveCatching extension",
        level = DeprecationLevel.ERROR,
        replaceWith = ReplaceWith("onReceiveCatching")
    ) // Warning since 1.3.0, error in 1.5.0, will be hidden or removed in 1.7.0
    public actual val onReceiveOrNull: SelectClause1<E?> get() = (this as BufferedChannel<E>).onReceiveOrNull
}

/**
 * Options for customizing channel async-iteration behavior.
 */
@JsExport
 // the deprecation message must be empty, or the API will be exported as deprecated to JS
@Deprecated(message = "", level = DeprecationLevel.HIDDEN)
public external interface ChannelIteratorOptions {
    /**
     * Controls whether the channel is canceled when iteration completes early.
     *
     * Equivalent TypeScript shape: `preventCancel?: boolean`.
     * Default is `false` when omitted.
     *
     * - `true`: do not cancel the channel on early iterator completion.
     * - `false` or omitted: cancel the channel on early iterator completion.
     */
    public val preventCancel: Boolean?
}

