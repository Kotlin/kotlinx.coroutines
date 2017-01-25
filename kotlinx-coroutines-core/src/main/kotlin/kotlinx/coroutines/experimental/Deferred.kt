package kotlinx.coroutines.experimental

import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.startCoroutine

/**
 * Deferred value is conceptually a non-blocking cancellable future.
 * It is created with [defer] coroutine builder.
 * It is in [active][isActive] state while the value is being computed.
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
 * The running coroutine is cancelled when the resulting object is [cancelled][Job.cancel].
 *
 * The [context] for the new coroutine must be explicitly specified.
 * See [CoroutineDispatcher] for the standard [context] implementations that are provided by `kotlinx.coroutines`.
 * The [context][CoroutineScope.context] of the parent coroutine from its [scope][CoroutineScope] may be used,
 * in which case the [Job] of the resulting coroutine is a child of the job of the parent coroutine.
 */
public fun <T> defer(context: CoroutineContext, block: suspend CoroutineScope.() -> T) : Deferred<T> =
    DeferredCoroutine<T>(newCoroutineContext(context)).apply {
        initParentJob(context[Job])
        block.startCoroutine(this, this)
    }

internal open class DeferredCoroutine<T>(
    context: CoroutineContext
) : AbstractCoroutine<T>(context), Deferred<T> {
    protected open fun start(): Boolean = false // LazyDeferredCoroutine overrides

    @Suppress("UNCHECKED_CAST")
    suspend override fun await(): T {
        // quick check if already complete (avoid extra object creation)
        getState().let { state ->
            if (state !is Active) {
                if (state is CompletedExceptionally) throw state.exception
                return state as T
            }
        }
        if (start()) { // LazyDeferredCoroutine overrides
            // recheck state (may have started & already completed
            getState().let { state ->
                if (state !is Active) {
                    if (state is CompletedExceptionally) throw state.exception
                    return state as T
                }
            }
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
