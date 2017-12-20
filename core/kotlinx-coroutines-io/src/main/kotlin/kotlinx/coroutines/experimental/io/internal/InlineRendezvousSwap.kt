package kotlinx.coroutines.experimental.io.internal

import kotlinx.atomicfu.*
import kotlinx.coroutines.experimental.*
import java.util.concurrent.CancellationException
import kotlin.coroutines.experimental.*
import kotlin.coroutines.experimental.intrinsics.*

/**
 * This is completely similar to [kotlinx.coroutines.experimental.channels.RendezvousChannel] except:
 * - non-cancellable
 * - all functions are inline and always tail-call suspend
 * - no poll/offer
 */
internal class InlineRendezvousSwap<T : Any> {
    private val senderCont = DelegatedContinuation<Unit>()
    private val receiverCont = DelegatedContinuation<T>()

    @Suppress("NOTHING_TO_INLINE")
    suspend inline fun send(e: T) = suspendCoroutineOrReturn<Unit> { c ->
        val result = try {
            senderCont.swap(c)
        } catch (t: Throwable) {
            receiverCont.resumeWithException(t)
            throw t
        }

        receiverCont.resume(e)
        result
    }

    @Suppress("NOTHING_TO_INLINE")
    suspend inline fun receive(): T = suspendCoroutineOrReturn { c ->
        val result = try {
            receiverCont.swap(c)
        } catch (t: Throwable) {
            senderCont.resumeWithException(t)
            throw t
        }

        senderCont.resume(Unit)
        result
    }

    internal class DelegatedContinuation<T : Any> : Continuation<T> {
        private val delegate = atomic<Continuation<T>?>(null)
        private var result: Any? = null
        private var e: Throwable? = null

        private fun reset() {
            delegate.getAndSet(null)?.takeUnless { it === this }?.resumeWithException(Cancellation)
            result = null
            e = null
        }

        fun swap(actual: Continuation<T>): Any? {
            require(actual !== this)

            delegate.update { c ->
                when {
                    c === this -> return result().also { reset() }
                    else -> actual
                }
            }

            return COROUTINE_SUSPENDED
        }

        private fun result(): Any? {
            e?.let { reset(); throw it }
            return result
        }

        override val context: CoroutineContext
            get() = delegate.value?.takeUnless { it === this }?.context ?: EmptyCoroutineContext

        override fun resumeWithException(exception: Throwable) {
            e = exception
            val c = delegate.getAndUpdate { c ->
                when {
                    c === this -> return
                    c == null -> this
                    else -> null
                }
            }

            if (c != null) {
                reset()
                c.resumeWithException(exception)
            }
        }

        override fun resume(value: T) {
            result = value
            val c = delegate.getAndUpdate { c ->
                when {
                    c === this -> return
                    c == null -> this
                    else -> null
                }
            }

            if (c != null) {
                reset()
                c.resume(value)
            }
        }
    }

    companion object {
        private val Cancellation = CancellationException()
    }
}

fun main(args: Array<String>) {
    val ch = InlineRendezvousSwap<String>()
    runBlocking {
        launch(coroutineContext) {
            repeat(2) {
                val e = ch.receive()
                println(e)
            }
        }
        launch(coroutineContext) {
            ch.send("1")
            ch.send("2")
        }
    }
}