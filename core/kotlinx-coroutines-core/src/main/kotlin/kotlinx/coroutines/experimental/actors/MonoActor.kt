package kotlinx.coroutines.experimental.actors

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*

/**
 * TODO document
 */
abstract class MonoActor<T>(
    context: CoroutineContext = DefaultDispatcher,
    parent: Job? = null,
    start: CoroutineStart = CoroutineStart.LAZY,
    channelCapacity: Int = 16
) : AbstractActor<T>(context, parent, start, channelCapacity) {


    suspend fun send(message: T) {
        job.start()
        mailbox.send(message)
    }

    protected abstract suspend fun receive(message: T)

    override suspend fun actorLoop() {
        try {
            for (message in mailbox) {
                try {
                    receive(message)
                } catch (e: Throwable) {
                    handleCoroutineException(actorContext, e)
                }
            }
        } finally {
            // Mailbox was closed, so it's time to cancel itself to properly kill all children and invoke cancellation handler
            job.cancel()
        }
    }
}

/**
 * TODO
 */
fun <T> actor(onMessage: suspend MonoActor<T>.(T) -> Unit): MonoActor<T> {
    return object : MonoActor<T>() {
        override suspend fun receive(message: T) {
            onMessage(message)
        }
    }
}
