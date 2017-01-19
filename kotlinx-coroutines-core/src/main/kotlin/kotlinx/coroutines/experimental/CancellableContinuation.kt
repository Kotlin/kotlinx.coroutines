package kotlinx.coroutines.experimental

import kotlin.coroutines.Continuation
import kotlin.coroutines.intrinsics.SUSPENDED_MARKER
import kotlin.coroutines.intrinsics.suspendCoroutineOrReturn
import kotlin.coroutines.suspendCoroutine

// --------------- cancellable continuations ---------------

/**
 * Cancellable continuation. Its job is completed when it is resumed or cancelled.
 * When [cancel] function is explicitly invoked, this continuation resumes with [CancellationException].
 * If the cancel reason was not a [CancellationException], then the original exception is added as cause of the
 * [CancellationException] that this continuation resumes with.
 */
public interface CancellableContinuation<in T> : Continuation<T>, Job

/**
 * Suspend coroutine similar to [suspendCoroutine], but provide an implementation of [CancellableContinuation] to
 * the [block].
 */
public inline suspend fun <T> suspendCancellableCoroutine(crossinline block: (CancellableContinuation<T>) -> Unit): T =
    suspendCoroutineOrReturn { c ->
        val safe = SafeCancellableContinuation(c)
        block(safe)
        safe.getResult()
    }

// --------------- implementation details ---------------

@PublishedApi
internal class SafeCancellableContinuation<in T>(
    private val delegate: Continuation<T>
) : AbstractCoroutine<T>(delegate.context), CancellableContinuation<T> {
    // only updated from the thread that invoked suspendCancellableCoroutine
    private var suspendedThread: Thread? = Thread.currentThread()

    fun getResult(): Any? {
        if (suspendedThread != null) {
            suspendedThread = null
            return SUSPENDED_MARKER
        }
        val state = getState()
        if (state is CompletedExceptionally) throw state.exception
        return state
    }

    @Suppress("UNCHECKED_CAST")
    override fun afterCompletion(state: Any?) {
        if (suspendedThread === Thread.currentThread()) {
            // cancelled during suspendCancellableCoroutine in its thread
            suspendedThread = null
        } else {
            // cancelled later or in other thread
            if (state is CompletedExceptionally)
                delegate.resumeWithException(state.exception)
            else
                delegate.resume(state as T)
        }
    }
}
