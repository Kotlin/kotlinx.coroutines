package kotlinx.coroutines

import kotlinx.atomicfu.*

@ExperimentalCoroutinesApi
public class Resource<T>(
    public val value: T,
    private val onCancellation: (value: T) -> Unit
) {
    private val _cancelled = atomic(false)

    public val isCancelled: Boolean
        get() = _cancelled.value

    public fun cancel() {
        if (!_cancelled.getAndSet(true)) onCancellation(value)
    }
}

internal fun callCancelResourceSafely(value: Resource<*>, resourceException: Throwable? = null): Throwable? {
    try {
        value.cancel()
    } catch (ex: Throwable) {
        if (resourceException != null) {
            resourceException.addSuppressedThrowable(ex)
        } else {
            return ex
        }
    }
    return resourceException
}
