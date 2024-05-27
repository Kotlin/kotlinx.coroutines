package kotlinx.coroutines.channels

import kotlinx.coroutines.channels.BufferOverflow.*
import kotlinx.coroutines.channels.ChannelResult.Companion.success
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*

/**
 * This is a special [BufferedChannel] extension that supports [DROP_OLDEST] and [DROP_LATEST]
 * strategies for buffer overflowing. This implementation ensures that `send(e)` never suspends,
 * either extracting the first element ([DROP_OLDEST]) or dropping the sending one ([DROP_LATEST])
 * when the channel capacity exceeds.
 */
internal open class ConflatedBufferedChannel<E>(
    private val capacity: Int,
    private val onBufferOverflow: BufferOverflow,
    onUndeliveredElement: OnUndeliveredElement<E>? = null
) : BufferedChannel<E>(capacity = capacity, onUndeliveredElement = onUndeliveredElement) {
    init {
        require(onBufferOverflow !== SUSPEND) {
            "This implementation does not support suspension for senders, use ${BufferedChannel::class.simpleName} instead"
        }
        require(capacity >= 1) {
            "Buffered channel capacity must be at least 1, but $capacity was specified"
        }
    }

    override val isConflatedDropOldest: Boolean
        get() = onBufferOverflow == DROP_OLDEST

    override suspend fun send(element: E) {
        // Should never suspend, implement via `trySend(..)`.
        trySendImpl(element, isSendOp = true).onClosed { // fails only when this channel is closed.
            onUndeliveredElement?.callUndeliveredElementCatchingException(element)?.let {
                it.addSuppressed(sendException)
                throw it
            }
            throw sendException
        }
    }

    override suspend fun sendBroadcast(element: E): Boolean {
        // Should never suspend, implement via `trySend(..)`.
        trySendImpl(element, isSendOp = true) // fails only when this channel is closed.
            .onSuccess { return true }
        return false
    }

    override fun trySend(element: E): ChannelResult<Unit> = trySendImpl(element, isSendOp = false)

    private fun trySendImpl(element: E, isSendOp: Boolean) =
        if (onBufferOverflow === DROP_LATEST) trySendDropLatest(element, isSendOp)
        else trySendDropOldest(element)

    private fun trySendDropLatest(element: E, isSendOp: Boolean): ChannelResult<Unit> {
        // Try to send the element without suspension.
        val result = super.trySend(element)
        // Complete on success or if this channel is closed.
        if (result.isSuccess || result.isClosed) return result
        // This channel is full. Drop the sending element.
        // Call the `onUndeliveredElement` lambda ONLY for 'send()' invocations,
        // for 'trySend()' it is responsibility of the caller
        if (isSendOp) {
            onUndeliveredElement?.callUndeliveredElementCatchingException(element)?.let {
                throw it
            }
        }
        return success(Unit)
    }

    @Suppress("UNCHECKED_CAST")
    override fun registerSelectForSend(select: SelectInstance<*>, element: Any?) {
        // The plain `send(..)` operation never suspends. Thus, either this
        // attempt to send the element succeeds or the channel is closed.
        // In any case, complete this `select` in the registration phase.
        trySend(element as E).let {
            it.onSuccess {
                select.selectInRegistrationPhase(Unit)
                return
            }.onClosed {
                select.selectInRegistrationPhase(CHANNEL_CLOSED)
                return
            }
        }
        error("unreachable")
    }

    override fun shouldSendSuspend() = false // never suspends.
}
