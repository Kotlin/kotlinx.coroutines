package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.coroutines.*

internal open class ChannelCoroutine<E>(
    parentContext: CoroutineContext,
    protected val _channel: Channel<E>,
    initParentJob: Boolean,
    active: Boolean
) : AbstractCoroutine<Unit>(parentContext, initParentJob, active), Channel<E> by _channel {

    val channel: Channel<E> get() = this

    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.2.0, binary compatibility with versions <= 1.1.x")
    override fun cancel() {
        cancelInternal(defaultCancellationException())
    }

    @Suppress("MULTIPLE_DEFAULTS_INHERITED_FROM_SUPERTYPES_DEPRECATION_WARNING") // do not remove the MULTIPLE_DEFAULTS suppression: required in K2
    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.2.0, binary compatibility with versions <= 1.1.x")
    final override fun cancel(cause: Throwable?): Boolean {
        cancelInternal(defaultCancellationException())
        return true
    }

    @Suppress("MULTIPLE_DEFAULTS_INHERITED_FROM_SUPERTYPES_DEPRECATION_WARNING") // do not remove the MULTIPLE_DEFAULTS suppression: required in K2
    final override fun cancel(cause: CancellationException?) {
        if (isCancelled) return // Do not create an exception if the coroutine (-> the channel) is already cancelled
        cancelInternal(cause ?: defaultCancellationException())
    }

    override fun cancelInternal(cause: Throwable) {
        val exception = cause.toCancellationException()
        _channel.cancel(exception) // cancel the channel
        cancelCoroutine(exception) // cancel the job
    }
}
