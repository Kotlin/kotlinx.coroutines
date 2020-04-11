package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlin.coroutines.*

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

internal fun callCancelResourceSafely(resource: Resource<*>, resourceException: ResourceCancellationException? = null): ResourceCancellationException? {
    try {
        resource.cancel()
    } catch (ex: Throwable) {
        if (resourceException != null) {
            resourceException.addSuppressedThrowable(ex)
        } else {
            return ResourceCancellationException("Exception in resource cancellation: ${resource.value}", ex)
        }
    }
    return resourceException
}

internal inline fun callCancelResource(resource: Resource<*>, context: () -> CoroutineContext) {
    callCancelResourceSafely(resource)?.let { ex ->
        handleCoroutineException(context(), ex)
    }
}

internal inline fun cancelResourceIfNeeded(resource: Any?, context: () -> CoroutineContext) {
    (resource as? Resource<*>)?.let { callCancelResource(it, context) }
}

internal class ResourceCancellationException(message: String, cause: Throwable) : RuntimeException(message, cause)
