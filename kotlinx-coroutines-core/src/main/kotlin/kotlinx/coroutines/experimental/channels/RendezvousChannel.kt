package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.CancellableContinuation
import kotlinx.coroutines.experimental.internal.LockFreeLinkedListHead
import kotlinx.coroutines.experimental.internal.LockFreeLinkedListNode
import kotlinx.coroutines.experimental.removeOnCompletion
import kotlinx.coroutines.experimental.suspendCancellableCoroutine

/**
 * Rendezvous channel. This channel does not have any buffer at all. An element is transferred from sender
 * to receiver only when [send] and [receive] invocations meet in time (rendezvous), so [send] suspends
 * until another coroutine invokes [receive] and [receive] suspends until another coroutine invokes [send].
 */
public class RendezvousChannel<E> : Channel<E> {
    private val queue = LockFreeLinkedListHead()

    // ------ SendChannel ------

    override val isClosedForSend: Boolean get() = queue.prev() is Closed<*>

    override val isFull: Boolean get() = queue.next() !is ReceiveOrClosed<*>

    suspend override fun send(element: E) {
        // fast path if receive is already waiting for rendezvous
        while (true) { // loop while there are receive waiters
            val receive = takeFirstReceiveOrPeekClosed() ?: break
            if (receive.tryResumeReceiveFromSend(element)) return // resumed it successfully
        }
        // slow-path does suspend
        return suspendCancellableCoroutine(true) sc@ { cont ->
            while (true) {
                val send = SendElement(cont, element) // must allocate fresh element on each loop
                if (queue.addLastIfPrev(send) { it !is Receive<*>  && it !is Closed<*> }) {
                    cont.initCancellability() // make it properly cancellable
                    cont.removeOnCompletion(send)
                    return@sc
                }
                // hm... there are already receivers (maybe), so try taking first
                takeFirstReceiveOrPeekClosed()?.also { receive ->
                    if (receive.tryResumeReceiveFromSend(element, cont)) return@sc
                }
            }
        }
    }

    override fun offer(element: E): Boolean {
        takeFirstReceiveOrPeekClosed()?.apply {
            tryResumeReceiveFromSend(element)
            return true
        }
        return false
    }

    override fun close() {
        while (true) {
            val receive = takeFirstReceiveOrPeekClosed()
            if (receive == null) {
                // queue empty or has only senders -- try add last "Closed" item to the queue
                if (queue.addLastIfPrev(Closed<E>()) { it !is Closed<*> }) return
            }
            if (receive is Closed<*>) return // already marked as closed -- nothing to do
            receive as Receive<E> // type assertion
            receive.resumeReceiveClosed()
        }
    }

    private fun takeFirstReceiveOrPeekClosed(): ReceiveOrClosed<E>? =
        queue.removeFirstIfIsInstanceOfOrPeekIf<ReceiveOrClosed<E>> { it is Closed<*> }

    // ------ ReceiveChannel ------

    override val isClosedForReceive: Boolean get() = queue.next() is Closed<*>

    override val isEmpty: Boolean get() = queue.next() !is Send<*>

    suspend override fun receive(): E {
        // fast path if send is already waiting for rendezvous or closed
        while (true) { // loop while there are send waiters
            val send = takeFirstSendOrPeekClosed() ?: break
            if (send.tryResumeSend()) return send.element // resumed it successfully
        }
        // slow-path does suspend
        return suspendCancellableCoroutine(true) sc@ { cont ->
            while (true) {
                val receive = ReceiveNonNull(cont) // must allocate fresh element on each loop
                if (queue.addLastIfPrev(receive) { it !is Send<*> }) {
                    cont.initCancellability() // make it properly cancellable
                    cont.removeOnCompletion(receive)
                    return@sc
                }
                // hm... there are already senders (maybe), so try taking first
                takeFirstSendOrPeekClosed()?.also { send ->
                    if (send.tryResumeSend()) {
                        send.resumeWithElement(cont)
                        return@sc
                    }
                }
            }
        }
    }

    suspend override fun receiveOrNull(): E? {
        // fast path if send is already waiting for rendezvous or closed
        while (true) { // loop while there are send waiters
            val send = takeFirstSendOrPeekClosed() ?: break
            if (send.tryResumeSend()) return send.elementOrNull // resumed it successfully
        }
        // slow-path does suspend
        return suspendCancellableCoroutine(true) sc@ { cont ->
            while (true) {
                val receive = ReceiveOrNull(cont) // must allocate fresh element on each loop
                if (queue.addLastIfPrev(receive) { it !is Send<*> }) {
                    cont.initCancellability() // make it properly cancellable
                    cont.removeOnCompletion(receive)
                    return@sc
                }
                // hm... there are already senders (maybe), so try taking first
                takeFirstSendOrPeekClosed()?.also { send ->
                    if (send.tryResumeSend()) {
                        send.resumeWithElementOrNull(cont)
                        return@sc
                    }
                }
            }
        }
    }

    override fun pool(): E? {
        while (true) {
            val waiter = takeFirstSendOrPeekClosed() ?: return null
            if (waiter.tryResumeSend()) return waiter.element
        }
    }

    override fun iterator(): ChannelIterator<E> = Iterator(this)

    private fun takeFirstSendOrPeekClosed(): Send<E>? =
        queue.removeFirstIfIsInstanceOfOrPeekIf<Send<E>> { it is Closed<*> }

    private companion object {
        val IS_UNKNOWN = 0
        val IS_HAS_VALUE = 1
        val IS_CLOSED = 2
    }

    private class Iterator<E>(val channel: RendezvousChannel<E>) : ChannelIterator<E> {
        var state: Int = IS_UNKNOWN
        var value: E? = null

        suspend override fun hasNext(): Boolean {
            when (state) {
                IS_HAS_VALUE -> return true
                IS_CLOSED -> return false
            }
            // fast path if send is already waiting for rendezvous
            while (true) { // loop while there are send waiters
                val send = channel.takeFirstSendOrPeekClosed() ?: break
                if (send.tryResumeSend()) return updateStateWithSend(send)
            }
            // slow-path does suspend
            return suspendCancellableCoroutine(true) sc@ { cont ->
                while (true) {
                    val receive = ReceiveHasNext(this, cont) // must allocate fresh element on each loop
                    if (channel.queue.addLastIfPrev(receive) { it !is Send<*> }) {
                        cont.initCancellability() // make it properly cancellable
                        cont.removeOnCompletion(receive)
                        return@sc
                    }
                    // hm... there are already senders (maybe), so try taking first
                    channel.takeFirstSendOrPeekClosed()?.also { send ->
                        if (send.tryResumeSend()) {
                            cont.resume(updateStateWithSend(send))
                            return@sc
                        }
                    }
                }
            }
        }

        private fun updateStateWithSend(send: Send<E>): Boolean {
            if (send is Closed<*>) {
                state = IS_CLOSED
                return false
            } else {
                state = IS_HAS_VALUE
                value = send.element
                return true
            }
        }

        suspend override fun next(): E {
            when (state) {
                IS_HAS_VALUE -> {
                    val value = this.value as E
                    this.state = IS_UNKNOWN
                    this.value = null
                    return value
                }
                IS_CLOSED -> throw ClosedReceiveChannelException()
            }
            // rare case when hasNext was not invoked yet -- just delegate to receive (leave state as IS_UNKNOWN)
            return channel.receive()
        }
    }

    private abstract class Send<out E> : LockFreeLinkedListNode() {
        abstract val element: E
        abstract val elementOrNull: E?
        abstract fun tryResumeSend(): Boolean
        abstract fun resumeWithElement(cont: CancellableContinuation<E>)
        abstract fun resumeWithElementOrNull(cont: CancellableContinuation<E?>)
    }

    private class SendElement<out E>(
            val cont: CancellableContinuation<Unit>,
            override val element: E
    ) : Send<E>() {
        override val elementOrNull: E? get() = element
        override fun tryResumeSend(): Boolean = cont.tryResume(Unit)
        override fun resumeWithElement(cont: CancellableContinuation<E>) = cont.resume(element)
        override fun resumeWithElementOrNull(cont: CancellableContinuation<E?>) = cont.resume(element)
    }

    private interface ReceiveOrClosed<in E> {
        fun tryResumeReceiveFromSend(value: E): Boolean
        fun tryResumeReceiveFromSend(value: E, cont: CancellableContinuation<Unit>): Boolean
    }

    private class Closed<E> : Send<E>(), ReceiveOrClosed<E> {
        override val element: E get() = throw ClosedReceiveChannelException()
        override val elementOrNull: E? get() = null
        override fun tryResumeSend(): Boolean = true
        override fun resumeWithElement(cont: CancellableContinuation<E>) = cont.resumeWithException(ClosedReceiveChannelException())
        override fun resumeWithElementOrNull(cont: CancellableContinuation<E?>) = cont.resume(null)
        override fun tryResumeReceiveFromSend(value: E): Boolean = throw ClosedSendChannelException()
        override fun tryResumeReceiveFromSend(value: E, cont: CancellableContinuation<Unit>): Boolean {
            cont.resumeWithException(ClosedSendChannelException())
            return true
        }
    }

    private abstract class Receive<in E> : LockFreeLinkedListNode(), ReceiveOrClosed<E> {
        override fun tryResumeReceiveFromSend(value: E, cont: CancellableContinuation<Unit>): Boolean {
            if (tryResumeReceiveFromSend(value)) {
                cont.resume(Unit)
                return true
            }
            return false
        }
        abstract fun resumeReceiveClosed()
    }

    private class ReceiveNonNull<in E>(val cont: CancellableContinuation<E>) : Receive<E>() {
        override fun tryResumeReceiveFromSend(value: E): Boolean = cont.tryResume(value)
        override fun resumeReceiveClosed() = cont.resumeWithException(ClosedReceiveChannelException())
    }

    private class ReceiveOrNull<in E>(val cont: CancellableContinuation<E?>) : Receive<E>() {
        override fun tryResumeReceiveFromSend(value: E): Boolean = cont.tryResume(value)
        override fun resumeReceiveClosed() = cont.resume(null)
    }

    private class ReceiveHasNext<E>(
            val iterator: Iterator<E>,
            val cont: CancellableContinuation<Boolean>
    ) : Receive<E>(), (Any?) -> Unit {
        override fun tryResumeReceiveFromSend(value: E): Boolean {
            iterator.value = value // tentative value (may fail to resume with it)
            return cont.tryResume(true, this)
        }

        override fun resumeReceiveClosed() {
            cont.tryResume(false, this)
        }

        // callback for tryResume onSuccess
        override fun invoke(hasNext: Any?) {
            hasNext as Boolean // try assertion -- that is the value we pass
            iterator.state = if (hasNext) IS_HAS_VALUE else IS_CLOSED
            if (!hasNext) iterator.value = null // cleanup tentative value
        }
    }
}

