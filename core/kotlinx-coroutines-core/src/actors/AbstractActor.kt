package kotlinx.coroutines.experimental.actors

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlin.coroutines.experimental.*

/**
 * Base class for actors implementation, which provides implementation for [ActorTraits]
 *
 * @param T type of messages which are stored in the mailbox
 */
abstract class AbstractActor<T>(
    context: CoroutineContext = DefaultDispatcher,
    parent: Job? = null,
    start: CoroutineStart = CoroutineStart.LAZY,
    channelCapacity: Int = 16
) : ActorTraits() {

    internal val mailbox = Channel<T>(channelCapacity)
    public final override val job: Job

    init {
        job = launch(context, start, parent) { actorLoop() }
        job.invokeOnCompletion { onClose() }
    }

    public override fun close() {
        mailbox.close()
    }

    public override fun kill() {
        job.cancel()
        mailbox.cancel()
    }

    private suspend fun actorLoop() {
        var exception: Throwable? = null
        try {
            onStart()
            for (message in mailbox) {
                onMessage(message)
            }
        } catch (e: Throwable) {
            exception = e
            handleCoroutineException(coroutineContext, e)
        } finally {
            job.cancel(exception)
            mailbox.close()
        }
    }

    internal abstract suspend fun onMessage(message: T)
}
