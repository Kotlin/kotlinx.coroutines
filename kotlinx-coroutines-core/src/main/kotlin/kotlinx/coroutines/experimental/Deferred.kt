package kotlinx.coroutines.experimental

import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.startCoroutine

/**
 * Deferred value is conceptually a non-blocking cancellable future.
 * It is created with [defer] coroutine builder.
 */
public interface Deferred<out T> : Job {
    /**
     * Awaits for completion of this value without blocking a thread and resumes when deferred computation is complete.
     * This suspending function is cancellable.
     * If the [Job] of the current coroutine is completed while this suspending function is waiting, this function
     * immediately resumes with [CancellationException].
     */
    public suspend fun await(): T

    /**
     * Returns *completed* result or throws [IllegalStateException] if this deferred value is still [isActive].
     * It throws the corresponding exception if this deferred has completed exceptionally.
     * This function is designed to be used from [onCompletion] handlers, when there is an absolute certainty that
     * the value is already complete.
     */
    public fun getCompleted(): T
}

/**
 * Starts new coroutine and returns its result as an implementation of [Deferred].
 * The running coroutine is cancelled when the resulting job is cancelled.
 * The [context] for the new coroutine must be explicitly specified and must include [CoroutineDispatcher] element.
 * See [CoroutineDispatcher] for the standard [context] implementations that are provided by `kotlinx.coroutines`.
 * The specified context is added to the context of the parent running coroutine (if any) inside which this function
 * is invoked. The [Job] of the resulting coroutine is a child of the job of the parent coroutine (if any).
 */
public fun <T> defer(context: CoroutineContext, block: suspend () -> T) : Deferred<T> =
    DeferredCoroutine<T>(newCoroutineContext(context)).also { block.startCoroutine(it) }

private class DeferredCoroutine<T>(
        parentContext: CoroutineContext
) : JobContinuation<T>(parentContext), Deferred<T> {
    @Suppress("UNCHECKED_CAST")
    suspend override fun await(): T {
        // quick check if already complete (avoid extra object creation)
        val state = getState()
        if (state !is Active) {
            if (state is CompletedExceptionally) throw state.exception
            return state as T
        }
        // Note: await is cancellable itself!
        return awaitGetValue()
    }

    @Suppress("UNCHECKED_CAST")
    private suspend fun awaitGetValue(): T = suspendCancellableCoroutine { cont ->
        cont.unregisterOnCompletion(onCompletion {
            val state = getState()
            check(state !is Active)
            if (state is CompletedExceptionally)
                cont.resumeWithException(state.exception)
            else
                cont.resume(state as T)
        })
    }

    @Suppress("UNCHECKED_CAST")
    override fun getCompleted(): T {
        val state = getState()
        check(state !is Active) { "This deferred value is still active" }
        if (state is CompletedExceptionally) throw state.exception
        return state as T
    }
}
