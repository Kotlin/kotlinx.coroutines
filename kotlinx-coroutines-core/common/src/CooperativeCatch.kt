package kotlinx.coroutines

/**
 * Calls the specified function [block] and returns its encapsulated result if invocation was successful.
 * If a [CancellationException] occurs during execution of the specified function [block], then it will
 * be immediately thrown. Otherwise, any other [Throwable] exception that was thrown from the [block]
 * function execution and encapsulating it as a failure.
 */
public inline fun <T, R> T.cooperativeCatch(block: T.() -> R): Result<R> {
    return try {
        Result.success(block())
    } catch (e: CancellationException) {
        throw e
    } catch (e: Throwable) {
        Result.failure(e)
    }
}

/**
 * Returns the encapsulated result of the given [transform] function applied to the encapsulated value
 * if this instance represents [success][Result.isSuccess]. If a [CancellationException] occurs during
 * the execution of the given [transform] function, it will be thrown immediately. Otherwise, the
 * original encapsulated [Throwable] exception if it is [failure][Result.isFailure].
 *
 * This function catches any [Throwable] exception thrown by [transform] function other than
 * [CancellationException], and encapsulates it as a failure.
 *
 * See [map] for an alternative that rethrows all exceptions from `transform` function.
 */
public inline fun <R, T> Result<T>.cooperativeMap(transform: (value: T) -> R): Result<R> {
    return getOrNull()?.let {
        cooperativeCatch { transform(it) }
    } ?: Result.failure(exceptionOrNull() ?: error("Unreachable state"))
}
