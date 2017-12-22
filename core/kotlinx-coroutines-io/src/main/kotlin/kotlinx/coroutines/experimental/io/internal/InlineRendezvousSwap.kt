package kotlinx.coroutines.experimental.io.internal

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.intrinsics.*

/**
 * This is completely similar to [kotlinx.coroutines.experimental.channels.RendezvousChannel] except:
 * - non-cancellable
 * - all functions are inline and always tail-call suspend
 * - no poll/offer
 */
internal class InlineRendezvousSwap<T : Any> {
    private val senderCont = MutableDelegateContinuation<Unit>()
    private val receiverCont = MutableDelegateContinuation<T>()

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