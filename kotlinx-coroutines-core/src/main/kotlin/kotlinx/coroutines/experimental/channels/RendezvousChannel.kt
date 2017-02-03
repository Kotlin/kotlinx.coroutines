package kotlinx.coroutines.experimental.channels

/**
 * Rendezvous channel. This channel does not have any buffer at all. An element is transferred from sender
 * to receiver only when [send] and [receive] invocations meet in time (rendezvous), so [send] suspends
 * until another coroutine invokes [receive] and [receive] suspends until another coroutine invokes [send].
 *
 * This implementation is fully lock-free.
 */
public class RendezvousChannel<E> : AbstractChannel<E>() {

    override val hasBuffer: Boolean get() = false
    override val isBufferEmpty: Boolean get() = true
    override val isBufferFull: Boolean get() = true

    // result is `OFFER_SUCCESS | OFFER_FAILED | Closed`
    override fun offerInternal(element: E): Any {
        while (true) {
            val receive = takeFirstReceiveOrPeekClosed() ?: return OFFER_FAILED
            val token = receive.tryResumeReceive(element)
            if (token != null) {
                receive.completeResumeReceive(token)
                return receive.offerResult
            }
        }
    }

    // result is `E | POLL_EMPTY | Closed`
    override fun pollInternal(): Any? {
        while (true) {
            val send = takeFirstSendOrPeekClosed() ?: return POLL_EMPTY
            val token = send.tryResumeSend()
            if (token != null) {
                send.completeResumeSend(token)
                return send.pollResult
            }
        }
    }
}

