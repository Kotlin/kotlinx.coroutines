package kotlinx.coroutines.experimental.actors

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*

/**
 *
 */
abstract class Actor(
    context: CoroutineContext = DefaultDispatcher,
    parent: Job? = null,
    start: CoroutineStart = CoroutineStart.LAZY,
    channelCapacity: Int = 16
) : AbstractActor<suspend () -> Unit>(context, parent, start, channelCapacity) {

    /**
     * TODO document
     */
    protected suspend fun act(block: suspend () -> Unit) {
        job.start()
        mailbox.send(block)
    }

    internal override suspend fun actorLoop() {
        try {
            for (action in mailbox) {
                try {
                    action()
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
