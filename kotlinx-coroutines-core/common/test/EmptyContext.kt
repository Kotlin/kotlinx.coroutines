package kotlinx.coroutines

import kotlinx.coroutines.internal.probeCoroutineCreated
import kotlinx.coroutines.internal.probeCoroutineResumed
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

suspend fun <T> withEmptyContext(block: suspend () -> T): T = suspendCoroutine { cont ->
    block.startCoroutineUnintercepted(Continuation(EmptyCoroutineContext) { cont.resumeWith(it) })
}

/**
 * Use this function to restart a coroutine directly from inside of [suspendCoroutine],
 * when the code is already in the context of this coroutine.
 * It does not use [ContinuationInterceptor] and does not update the context of the current thread.
 */
fun <T> (suspend () -> T).startCoroutineUnintercepted(completion: Continuation<T>) {
    val actualCompletion = probeCoroutineCreated(completion)
    val value = try {
        probeCoroutineResumed(actualCompletion)
        startCoroutineUninterceptedOrReturn(actualCompletion)
    } catch (e: Throwable) {
        actualCompletion.resumeWithException(e)
        return
    }
    if (value !== COROUTINE_SUSPENDED) {
        @Suppress("UNCHECKED_CAST")
        actualCompletion.resume(value as T)
    }
}
