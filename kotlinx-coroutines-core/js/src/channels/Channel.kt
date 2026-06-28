@file:OptIn(ExperimentalJsExport::class, ExperimentalStdlibApi::class)
@file:Suppress("EXPOSED_FUNCTION_RETURN_TYPE", "INVISIBLE_REFERENCE", "EXPOSED_SUPER_INTERFACE")
package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.recoverStackTrace
import kotlinx.coroutines.selects.*
import kotlinx.js.JsPlainObject
import kotlin.internal.*
import kotlin.js.Promise
import kotlin.coroutines.EmptyCoroutineContext

@JsImplicitExport(couldBeConvertedToExplicitExport = true)
public actual interface SendChannel<in E> {
    @DelicateCoroutinesApi
    public actual val isClosedForSend: Boolean

    public actual suspend fun send(element: E)
    public actual fun close(cause: Throwable?): Boolean
    public actual fun invokeOnClose(handler: (cause: Throwable?) -> Unit)

    @JsExport.Ignore // Can't be exported until the compiler supports exporting of value classes
    public actual fun trySend(element: E): ChannelResult<Unit>

    @JsExport.Ignore // Is not so easy to use on the JavaScript side, because it's implemented with the contextual operator invoke
    public actual val onSend: SelectClause2<E, SendChannel<E>>

    @Deprecated(
        level = DeprecationLevel.ERROR,
        message = "Deprecated in the favour of 'trySend' method",
        replaceWith = ReplaceWith("trySend(element).isSuccess")
    ) // Warning since 1.5.0, error since 1.6.0, not hidden until 1.8+ because API is quite widespread
    @JsExport.Ignore
    public actual fun offer(element: E): Boolean {
        val result = trySend(element)
        if (result.isSuccess) return true
        throw recoverStackTrace(result.exceptionOrNull() ?: return false)
    }
}

@JsImplicitExport(couldBeConvertedToExplicitExport = true)
public actual interface ReceiveChannel<out E> : JsAsyncIterable<E> {
    @DelicateCoroutinesApi
    public actual val isClosedForReceive: Boolean
    @ExperimentalCoroutinesApi
    public actual val isEmpty: Boolean

    public actual suspend fun receive(): E
    public actual fun cancel(cause: CancellationException?)

    override fun asyncIterator(): JsAsyncIterator<E> =
        asyncIterator(CoroutineScope(EmptyCoroutineContext))

    @JsExport.Ignore
    // For Kotlin side only to be able to set up a custom scope for the iterator
    public fun asyncIterator(scope: CoroutineScope): JsAsyncIterator<E> =
        JsAsyncIterator(
            next = {
                scope.promise {
                    val result = receiveCatching()
                    if (result.isClosed) {
                        when (val cause = result.exceptionOrNull()) {
                            null, is CancellationException -> JsIteratorResult(done = true)
                            else -> throw cause
                        }
                    } else {
                        JsIteratorResult(value = result.getOrThrow(), done = false)
                    }
                }
            },
            `return` = { value: @UnsafeVariance E ->
                cancel(null)
                Promise.resolve(JsIteratorResult(value = value, done = true))
            }.unsafeCast<() -> Promise<JsIteratorResult<E>>>(),
            `throw` = { err: dynamic ->
                cancel(CancellationException("Channel was closed via AsyncIterator#throw method", err))
                Promise.reject(err)
            }
        )

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

@JsName("AsyncIterable")
internal external interface JsAsyncIterable<out T> {
    @JsSymbol("asyncIterator")
    public fun asyncIterator(): JsAsyncIterator<T>
}

@JsPlainObject
@JsName("AsyncIterator")
internal external interface JsAsyncIterator<out T> {
    public val next: () -> Promise<JsIteratorResult<T>>
    public val `return`: () -> Promise<JsIteratorResult<T>>
    public val `throw`: (value: Any?) -> Promise<JsIteratorResult<T>>
}

@JsPlainObject
@JsName("IteratorResult")
internal external interface JsIteratorResult<out T> {
    public val value: T?
    public val done: Boolean
}
