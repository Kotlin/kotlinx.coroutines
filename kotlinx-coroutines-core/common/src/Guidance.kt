package kotlinx.coroutines

import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext

/**
 * @suppress this is a function that should help users who are trying to use 'launch'
 * without the corresponding coroutine scope. It is not supposed to be called.
 */
@Deprecated("'launch' can not be called without the corresponding coroutine scope. " +
    "Consider wrapping 'launch' in 'coroutineScope { }', using 'runBlocking { }', " +
    "or using some other 'CoroutineScope'", level = DeprecationLevel.ERROR)
@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
@kotlin.internal.LowPriorityInOverloadResolution
public fun launch(
    context: CoroutineContext = EmptyCoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> Unit
): Job {
    throw UnsupportedOperationException("Should never be called, was introduced to help with incomplete code")
}

/**
 * @suppress this is a function that should help users who are trying to use 'launch'
 * without the corresponding coroutine scope. It is not supposed to be called.
 */
@Deprecated("'async' can not be called without the corresponding coroutine scope. " +
    "Consider wrapping 'async' in 'coroutineScope { }', using 'runBlocking { }', " +
    "or using some other 'CoroutineScope'", level = DeprecationLevel.ERROR)
@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
@kotlin.internal.LowPriorityInOverloadResolution
public fun <T> async(
    context: CoroutineContext = EmptyCoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> T
): Deferred<T> {
    throw UnsupportedOperationException("Should never be called, was introduced to help with incomplete code")
}
