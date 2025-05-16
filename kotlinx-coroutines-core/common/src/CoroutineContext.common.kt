package kotlinx.coroutines

import kotlin.coroutines.*

/**
 * Creates a context for a new coroutine.
 *
 * This function is used by coroutine builders to create a new coroutine context.
 * - It installs [Dispatchers.Default] when no other dispatcher or [ContinuationInterceptor] is specified.
 * - On the JVM, if the debug mode is enabled, it assigns a unique identifier to every coroutine for tracking it.
 * - On the JVM, copyable thread-local elements from [CoroutineScope.coroutineContext] and [context]
 *   are copied and combined as needed.
 * - The elements of [context] and [CoroutineScope.coroutineContext] other than copyable thread-context ones
 *   are combined as is, with the elements from [context] overriding the elements from [CoroutineScope.coroutineContext]
 *   in case of equal [keys][CoroutineContext.Key].
 *
 * See the documentation of this function's JVM implementation for platform-specific details.
 */
public expect fun CoroutineScope.newCoroutineContext(context: CoroutineContext): CoroutineContext

/**
 * Creates a context for coroutine builder functions that do not launch a new coroutine, e.g. [withContext].
 * @suppress
 */
@InternalCoroutinesApi
public expect fun CoroutineContext.newCoroutineContext(addedContext: CoroutineContext): CoroutineContext

@PublishedApi // to have unmangled name when using from other modules via suppress
@Suppress("PropertyName")
internal expect val DefaultDelay: Delay

// countOrElement -- pre-cached value for ThreadContext.kt
internal expect inline fun <T> withCoroutineContext(context: CoroutineContext, countOrElement: Any?, block: () -> T): T
internal expect inline fun <T> withContinuationContext(continuation: Continuation<*>, countOrElement: Any?, block: () -> T): T
internal expect fun Continuation<*>.toDebugString(): String
internal expect val CoroutineContext.coroutineName: String?
