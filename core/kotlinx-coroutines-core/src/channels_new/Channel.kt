package channels_new

import kotlinx.coroutines.CancellableContinuation

interface Channel<E> {
    suspend fun send(element: E)
    fun offer(element: E): Boolean

    suspend fun receive(): E
    fun poll(): E?

    val onSend: Param1RegInfo<Unit>
    val onReceive: Param0RegInfo<E>
}

interface Cleanable {
    fun clean(index: Int)
}

internal fun <T> CancellableContinuation<T>.tryResumeCont(value: T): Boolean {
    // Token is null if this continuation is cancelled
    val token = tryResume(value) ?: return false
    // This continuation can be resumed, complete and return `true`
    completeResume(token)
    return true
}