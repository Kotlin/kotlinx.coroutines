package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.*

/**
 * Implementation note: `owner` is an internal marked that is used ONLY for identity checks by coroutines machinery,
 * and it's never exposed, thus it's safe to have it both `@Transient` and non-nullable.
 */
internal actual class AbortFlowException actual constructor(
    @JvmField @Transient actual val owner: Any
) : CancellationException("Flow was aborted, no more elements needed") {

    override fun fillInStackTrace(): Throwable {
        if (DEBUG) return super.fillInStackTrace()
        // Prevent Android <= 6.0 bug, #1866
        stackTrace = emptyArray()
        return this
    }
}

internal actual class ChildCancelledException : CancellationException("Child of the scoped flow was cancelled") {
    override fun fillInStackTrace(): Throwable {
        if (DEBUG) return super.fillInStackTrace()
        // Prevent Android <= 6.0 bug, #1866
        stackTrace = emptyArray()
        return this
    }
}
