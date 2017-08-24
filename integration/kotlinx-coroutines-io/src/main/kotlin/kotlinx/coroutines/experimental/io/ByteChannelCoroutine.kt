package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*

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
