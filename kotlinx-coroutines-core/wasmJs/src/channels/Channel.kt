package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.recoverStackTrace
import kotlinx.coroutines.selects.*
import kotlin.internal.*

public actual interface SendChannel<in E> {
    @DelicateCoroutinesApi
    public actual val isClosedForSend: Boolean
    public actual suspend fun send(element: E)
    public actual val onSend: SelectClause2<E, SendChannel<E>>
    public actual fun trySend(element: E): ChannelResult<Unit>
    public actual fun close(cause: Throwable?): Boolean
    public actual fun invokeOnClose(handler: (cause: Throwable?) -> Unit)

    @Deprecated(
        level = DeprecationLevel.ERROR,
        message = "Deprecated in the favour of 'trySend' method",
        replaceWith = ReplaceWith("trySend(element).isSuccess")
    ) // Warning since 1.5.0, error since 1.6.0, not hidden until 1.8+ because API is quite widespread
    public actual fun offer(element: E): Boolean {
        val result = trySend(element)
        if (result.isSuccess) return true
        throw recoverStackTrace(result.exceptionOrNull() ?: return false)
    }
}

public actual interface ReceiveChannel<out E> {
    @DelicateCoroutinesApi
    public actual val isClosedForReceive: Boolean
    @ExperimentalCoroutinesApi
    public actual val isEmpty: Boolean
    public actual suspend fun receive(): E
    public actual val onReceive: SelectClause1<E>
    public actual suspend fun receiveCatching(): ChannelResult<E>
    public actual val onReceiveCatching: SelectClause1<ChannelResult<E>>
    public actual fun tryReceive(): ChannelResult<E>
    public actual operator fun iterator(): ChannelIterator<E>
    public actual fun cancel(cause: CancellationException?)

    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.2.0, binary compatibility with versions <= 1.1.x")
    public actual fun cancel(cause: Throwable?): Boolean

    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.2.0, binary compatibility with versions <= 1.1.x")
    public actual fun cancel(): Unit = cancel(null)

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
