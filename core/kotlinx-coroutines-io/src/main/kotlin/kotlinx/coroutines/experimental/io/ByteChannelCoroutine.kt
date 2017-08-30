package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.AbstractCoroutine
import kotlinx.coroutines.experimental.JobSupport
import kotlinx.coroutines.experimental.handleCoroutineException
import kotlin.coroutines.experimental.CoroutineContext

internal open class ByteChannelCoroutine(
    parentContext: CoroutineContext,
    open val channel: ByteChannel
) : AbstractCoroutine<Unit>(parentContext, active = true) {
    override fun afterCompletion(state: Any?, mode: Int) {
        val cause = (state as? JobSupport.CompletedExceptionally)?.cause
        if (!channel.close(cause) && cause != null)
            handleCoroutineException(context, cause)

        super.afterCompletion(state, mode)
    }
}
