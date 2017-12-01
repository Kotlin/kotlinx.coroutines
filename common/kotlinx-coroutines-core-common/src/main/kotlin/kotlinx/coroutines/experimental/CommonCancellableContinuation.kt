package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.Continuation

public expect interface CancellableContinuation<in T> : Continuation<T> {
    public val isActive: Boolean
    public val isCompleted: Boolean
    public val isCancelled: Boolean
    @Suppress("EXPECTED_DECLARATION_WITH_DEFAULT_PARAMETER")
    public fun tryResume(value: T, idempotent: Any? = null): Any?
    public fun completeResume(token: Any)
    public fun initCancellability()
    @Suppress("EXPECTED_DECLARATION_WITH_DEFAULT_PARAMETER")
    public actual fun cancel(cause: Throwable? = null): Boolean
    public fun invokeOnCompletion(handler: CompletionHandler): DisposableHandle
    public fun CoroutineDispatcher.resumeUndispatched(value: T)
    public fun CoroutineDispatcher.resumeUndispatchedWithException(exception: Throwable)
}

@Suppress("EXPECTED_DECLARATION_WITH_DEFAULT_PARAMETER")
public expect suspend fun <T> suspendCancellableCoroutine(
    holdCancellability: Boolean = false,
    block: (CancellableContinuation<T>) -> Unit
): T

@Suppress("EXPECTED_DECLARATION_WITH_DEFAULT_PARAMETER")
public expect suspend fun <T> suspendAtomicCancellableCoroutine(
    holdCancellability: Boolean = false,
    block: (CancellableContinuation<T>) -> Unit
): T
