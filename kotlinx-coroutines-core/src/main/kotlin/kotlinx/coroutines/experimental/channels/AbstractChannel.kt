package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.CancellableContinuation
import kotlinx.coroutines.experimental.internal.LockFreeLinkedListHead
import kotlinx.coroutines.experimental.internal.LockFreeLinkedListNode
import kotlinx.coroutines.experimental.removeOnCompletion
import kotlinx.coroutines.experimental.suspendCancellableCoroutine

/**
 * Abstract channel. It is a base class for buffered and unbuffered channels.
 */
public abstract class AbstractChannel<E> : Channel<E> {
    private val queue = LockFreeLinkedListHead()

    // ------ extension points for buffered channels ------

    protected abstract val hasBuffer: Boolean
    protected abstract val isBufferEmpty: Boolean
    protected abstract val isBufferFull: Boolean

    /**
     * Tries to add element to buffer or to queued receiver.
     * Return type is `OFFER_SUCCESS | OFFER_FAILED | OFFER_CLOSED`.
     */
    protected abstract fun offerInternal(element: E): Int

    /**
     * Tries to remove element from buffer or from queued sender.
     * Return type is `E | POLL_EMPTY | POLL_CLOSED`
     */
    protected abstract fun pollInternal(): Any?


    // ------ state function for concrete implementations ------

    protected val isClosedTokenFirstInQueue: Boolean get() = queue.next() is Closed<*>

    // ------ SendChannel ------

    override val isClosedForSend: Boolean get() = queue.prev() is Closed<*>
    override val isFull: Boolean get() = queue.next() !is ReceiveOrClosed<*> && isBufferFull

    suspend override fun send(element: E) {
        // fast path -- try offer non-blocking
        if (offer(element)) return
        // slow-path does suspend
        return sendSuspend(element)
    }

    override fun offer(element: E): Boolean =
        when (offerInternal(element)) {
            OFFER_SUCCESS -> true
            OFFER_FAILED -> false
            else -> throw ClosedSendChannelException()
        }

    private suspend fun sendSuspend(element: E): Unit = suspendCancellableCoroutine(true) sc@ { cont ->
        val send = SendElement(cont, element)
        loop@ while (true) {
            if (enqueueSend(send)) {
                cont.initCancellability() // make it properly cancellable
                cont.removeOnCompletion(send)
                return@sc
            }
            // hm... something is not right. try to offer
            when (offerInternal(element)) {
                OFFER_SUCCESS -> {
                    cont.resume(Unit)
                    return@sc
                }
                OFFER_CLOSED -> {
                    cont.resumeWithException(ClosedSendChannelException())
                    return@sc
                }
            }
        }
    }

    private fun enqueueSend(send: SendElement) =
        if (hasBuffer)
            queue.addLastIfPrevAndIf(send, { it !is ReceiveOrClosed<*> }, { isBufferFull })
        else
            queue.addLastIfPrev(send, { it !is ReceiveOrClosed<*> })

    override fun close() {
        while (true) {
            val receive = takeFirstReceiveOrPeekClosed()
            if (receive == null) {
                // queue empty or has only senders -- try add last "Closed" item to the queue
                if (queue.addLastIfPrev(Closed<E>(), { it !is ReceiveOrClosed<*> })) return
                continue // retry on failure
            }
            if (receive is Closed<*>) return // already marked as closed -- nothing to do
            receive as Receive<E> // type assertion
            receive.resumeReceiveClosed()
        }
    }

    protected fun takeFirstReceiveOrPeekClosed(): ReceiveOrClosed<E>? =
        queue.removeFirstIfIsInstanceOfOrPeekIf<ReceiveOrClosed<E>> { it is Closed<*> }

    // ------ ReceiveChannel ------

    override val isClosedForReceive: Boolean get() = isClosedTokenFirstInQueue && isBufferEmpty
    override val isEmpty: Boolean get() = queue.next() !is Send && isBufferEmpty

    @Suppress("UNCHECKED_CAST")
    suspend override fun receive(): E {
        // fast path -- try poll non-blocking
        val result = pollInternal()
        if (result === POLL_CLOSED) throw ClosedReceiveChannelException()
        if (result !== POLL_EMPTY) return result as E
        // slow-path does suspend
        return receiveSuspend()
    }

    @Suppress("UNCHECKED_CAST")
    private suspend fun receiveSuspend(): E = suspendCancellableCoroutine(true) sc@ { cont ->
        val receive = ReceiveNonNull(cont)
        while (true) {
            if (enqueueReceive(receive)) {
                cont.initCancellability() // make it properly cancellable
                cont.removeOnCompletion(receive)
                return@sc
            }
            // hm... something is not right. try to poll
            val result = pollInternal()
            if (result === POLL_CLOSED) {
                cont.resumeWithException(ClosedReceiveChannelException())
                return@sc
            }
            if (result !== POLL_EMPTY) {
                cont.resume(result as E)
                return@sc
            }
        }
    }

    private fun enqueueReceive(receive: Receive<E>) =
        if (hasBuffer)
            queue.addLastIfPrevAndIf(receive, { it !is Send }, { isBufferEmpty })
        else
            queue.addLastIfPrev(receive, { it !is Send })

    @Suppress("UNCHECKED_CAST")
    suspend override fun receiveOrNull(): E? {
        // fast path -- try poll non-blocking
        val result = pollInternal()
        if (result === POLL_CLOSED) return null
        if (result !== POLL_EMPTY) return result as E
        // slow-path does suspend
        return receiveOrNullSuspend()
    }

    @Suppress("UNCHECKED_CAST")
    private suspend fun receiveOrNullSuspend(): E? = suspendCancellableCoroutine(true) sc@ { cont ->
        val receive = ReceiveOrNull(cont)
        while (true) {
            if (enqueueReceive(receive)) {
                cont.initCancellability() // make it properly cancellable
                cont.removeOnCompletion(receive)
                return@sc
            }
            // hm... something is not right. try to poll
            val result = pollInternal()
            if (result === POLL_CLOSED) {
                cont.resume(null)
                return@sc
            }
            if (result !== POLL_EMPTY) {
                cont.resume(result as E)
                return@sc
            }
        }
    }

    @Suppress("UNCHECKED_CAST")
    override fun poll(): E? {
        val result = pollInternal()
        return if (result === POLL_EMPTY || result === POLL_CLOSED) null else result as E
    }

    override fun iterator(): ChannelIterator<E> = Iterator(this)

    protected fun takeFirstSendOrPeekClosed(): Send? =
        queue.removeFirstIfIsInstanceOfOrPeekIf<Send> { it is Closed<*> }

    protected companion object {
        const val OFFER_SUCCESS = 0
        const val OFFER_FAILED = 1
        const val OFFER_CLOSED = 2

        val POLL_EMPTY: Any = Marker("POLL_EMPTY")
        val POLL_CLOSED: Any = Marker("POLL_CLOSED")
    }

    // for debugging
    private class Marker(val string: String) {
        override fun toString(): String = string
    }

    private class Iterator<E>(val channel: AbstractChannel<E>) : ChannelIterator<E> {
        var result: Any? = POLL_EMPTY // E | POLL_CLOSED | POLL_EMPTY

        suspend override fun hasNext(): Boolean {
            // check for repeated hasNext
            if (result !== POLL_EMPTY) return result !== POLL_CLOSED
            // fast path -- try poll non-blocking
            result = channel.pollInternal()
            if (result !== POLL_EMPTY) return result !== POLL_CLOSED
            // slow-path does suspend
            return hasNextSuspend()
        }

        private suspend fun hasNextSuspend(): Boolean = suspendCancellableCoroutine(true) sc@ { cont ->
            val receive = ReceiveHasNext(this, cont)
            while (true) {
                if (channel.enqueueReceive(receive)) {
                    cont.initCancellability() // make it properly cancellable
                    cont.removeOnCompletion(receive)
                    return@sc
                }
                // hm... something is not right. try to poll
                result = channel.pollInternal()
                if (result === POLL_CLOSED) {
                    cont.resume(false)
                    return@sc
                }
                if (result !== POLL_EMPTY) {
                    cont.resume(true)
                    return@sc
                }
            }
        }

        @Suppress("UNCHECKED_CAST")
        suspend override fun next(): E {
            if (result === POLL_CLOSED) throw ClosedReceiveChannelException()
            if (result !== POLL_EMPTY) {
                val value = this.result as E
                this.result = POLL_EMPTY
                return value
            }
            // rare case when hasNext was not invoked yet -- just delegate to receive (leave state as is)
            return channel.receive()
        }
    }

    protected interface Send {
        val pollResult: Any? // E | POLL_CLOSED
        fun tryResumeSend(): Any?
        fun completeResumeSend(token: Any)
    }

    protected interface ReceiveOrClosed<in E> {
        val offerResult: Int // OFFER_SUCCESS | OFFER_CLOSED
        fun tryResumeReceive(value: E): Any?
        fun completeResumeReceive(token: Any)
    }

    @Suppress("UNCHECKED_CAST")
    private class SendElement(
            val cont: CancellableContinuation<Unit>,
            override val pollResult: Any?
    ) : LockFreeLinkedListNode(), Send {
        override fun tryResumeSend(): Any? = cont.tryResume(Unit)
        override fun completeResumeSend(token: Any) = cont.completeResume(token)
    }

    private class Closed<in E> : LockFreeLinkedListNode(), Send, ReceiveOrClosed<E> {
        override val offerResult get() = OFFER_CLOSED
        override val pollResult get() = POLL_CLOSED
        override fun tryResumeSend(): Boolean = true
        override fun completeResumeSend(token: Any) {}
        override fun tryResumeReceive(value: E): Any? = throw ClosedSendChannelException()
        override fun completeResumeReceive(token: Any) = throw ClosedSendChannelException()
    }

    private abstract class Receive<in E> : LockFreeLinkedListNode(), ReceiveOrClosed<E> {
        override val offerResult get() = OFFER_SUCCESS
        abstract fun resumeReceiveClosed()
    }

    private class ReceiveNonNull<in E>(val cont: CancellableContinuation<E>) : Receive<E>() {
        override fun tryResumeReceive(value: E): Any? = cont.tryResume(value)
        override fun completeResumeReceive(token: Any) = cont.completeResume(token)
        override fun resumeReceiveClosed() = cont.resumeWithException(ClosedReceiveChannelException())
    }

    private class ReceiveOrNull<in E>(val cont: CancellableContinuation<E?>) : Receive<E>() {
        override fun tryResumeReceive(value: E): Any? = cont.tryResume(value)
        override fun completeResumeReceive(token: Any) = cont.completeResume(token)
        override fun resumeReceiveClosed() = cont.resume(null)
    }

    private class ReceiveHasNext<E>(
            val iterator: Iterator<E>,
            val cont: CancellableContinuation<Boolean>
    ) : Receive<E>() {
        override fun tryResumeReceive(value: E): Any? {
            val token = cont.tryResume(true)
            if (token != null) iterator.result = value
            return token
        }

        override fun completeResumeReceive(token: Any) = cont.completeResume(token)

        override fun resumeReceiveClosed() {
            val token = cont.tryResume(false)
            if (token != null) {
                iterator.result = POLL_CLOSED
                cont.completeResume(token)
            }
        }
    }
}

