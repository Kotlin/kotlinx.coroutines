package kotlinx.coroutines

import java.util.concurrent.atomic.AtomicReference

suspend fun <T> runWithCurrentContinuation(
        block: (Continuation<T>) -> Unit
): T = suspendWithCurrentContinuation { continuation ->
    val safe = SafeContinuation(continuation)
    block(safe)
    safe.returnResult()
}

private class SafeContinuation<in T>(val delegate: Continuation<T>) : Continuation<T> {
    // consensus on result with asynchronous calls to continuation
    val result = AtomicReference<Any?>(Undecided)

    override fun resume(data: T) {
        if (result.compareAndSet(Undecided, data)) return
        delegate.resume(data)
    }

    override fun resumeWithException(exception: Throwable) {
        if (result.compareAndSet(Undecided, Fail(exception))) return
        delegate.resumeWithException(exception)
    }

    fun returnResult(): Any? {
        if (result.get() == Undecided) result.compareAndSet(Undecided, Suspend)
        val result = result.get()
        if (result is Fail) throw result.e else return result
    }
}

private object Undecided
private class Fail(val e: Throwable)