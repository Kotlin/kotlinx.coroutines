@file:OptIn(ExperimentalJsExport::class)
@file:Suppress("EXPOSED_FUNCTION_RETURN_TYPE", "INVISIBLE_REFERENCE", "EXPOSED_SUPER_INTERFACE")
package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.JsAsyncIterable
import kotlinx.coroutines.internal.recoverStackTrace
import kotlinx.coroutines.selects.*
import kotlin.internal.*
import kotlin.js.Promise
import kotlinx.coroutines.internal.JsAsyncIterator
import kotlinx.coroutines.internal.JsIteratorResult

@JsImplicitExport(couldBeConvertedToExplicitExport = true)
public actual interface ReceiveChannel<out E> : JsAsyncIterable<E> {
    @DelicateCoroutinesApi
    public actual val isClosedForReceive: Boolean
    @ExperimentalCoroutinesApi
    public actual val isEmpty: Boolean

    public actual suspend fun receive(): E
    public actual fun cancel(cause: CancellationException?)

    /**
     * Returns a JavaScript `AsyncIterator` for this channel.
     *
     * This method is used to implement the JavaScript async-iteration protocol, so that a
     * `ReceiveChannel` exported to JavaScript can be consumed with `for await ... of`.
     *
     * Each call to the iterator's `next` method receives at most one element from this channel:
     *
     * - if an element is available, the returned `Promise` is fulfilled with an iterator result
     *   whose `value` is the received element and whose `done` is `false`;
     * - if the channel is closed normally, or is cancelled with a [CancellationException], the
     *   returned `Promise` is fulfilled with an iterator result whose `done` is `true`;
     * - if the channel is closed with another cause, the returned `Promise` is rejected with that
     *   cause.
     *
     * Calling the iterator's `return` method finishes this iterator instance and returns a fulfilled
     * `Promise` with `done` set to `true`. It does not cancel the underlying channel.
     *
     * Calling the iterator's `throw` method finishes this iterator instance and returns a rejected
     * `Promise` with the supplied error. It does not cancel the underlying channel.
     *
     * The coroutines backing calls to `next` are started in [GlobalScope].
     * In particular, they are not children of any caller-provided coroutine
     * scope and therefore are not bound to the lifetime of any structured-concurrency scope.
     */
    override fun asyncIterator(): JsAsyncIterator<E> {
        var wasEarlyFinished = false
        return JsAsyncIterator(
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
            `return` = { value: E? ->
                wasEarlyFinished = true
                Promise.resolve(JsIteratorResult(value = value, done = true))
            },
            `throw` = { err: dynamic ->
                wasEarlyFinished = true
                Promise.reject(err)
            }
        )
    }

    @JsExport.Ignore // Is replaced by AsyncIterable implementation
    public actual operator fun iterator(): ChannelIterator<E>

    @JsExport.Ignore // Can't be exported until the compiler supports exporting of value classes
    public actual fun tryReceive(): ChannelResult<E>

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

