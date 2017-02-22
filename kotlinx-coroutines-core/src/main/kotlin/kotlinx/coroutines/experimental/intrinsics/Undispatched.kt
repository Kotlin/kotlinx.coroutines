package kotlinx.coroutines.experimental.intrinsics

import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.intrinsics.COROUTINE_SUSPENDED
import kotlin.coroutines.experimental.suspendCoroutine

/**
 * Use this function to restart coroutine directly from inside of [suspendCoroutine].
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
@Suppress("PLATFORM_CLASS_MAPPED_TO_KOTLIN", "UNCHECKED_CAST")
internal fun <R> (suspend () -> R).startUndispatchedCoroutine(completion: Continuation<R>) {
    val value = try {
        (this as kotlin.jvm.functions.Function1<Continuation<R>, Any?>).invoke(completion)
    } catch (e: Throwable) {
        completion.resumeWithException(e)
        return
    }
    if (value !== COROUTINE_SUSPENDED)
        completion.resume(value as R)
}

/**
 * Use this function to restart coroutine directly from inside of [suspendCoroutine].
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
@Suppress("PLATFORM_CLASS_MAPPED_TO_KOTLIN", "UNCHECKED_CAST")
internal fun <E, R> (suspend (E) -> R).startUndispatchedCoroutine(element: E, completion: Continuation<R>) {
    val value = try {
        (this as kotlin.jvm.functions.Function2<E, Continuation<R>, Any?>).invoke(element, completion)
    } catch (e: Throwable) {
        completion.resumeWithException(e)
        return
    }
    if (value !== COROUTINE_SUSPENDED)
        completion.resume(value as R)
}
