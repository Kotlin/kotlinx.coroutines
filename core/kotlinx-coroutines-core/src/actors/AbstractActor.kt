package kotlinx.coroutines.experimental.actors

import kotlinx.atomicfu.*
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlin.coroutines.experimental.*

/**
 * Base class for actors implementation, which provides implementation for [ActorTraits]
 * This class is not designed to be extended outside of kotlinx.coroutines, so it's internal
 *
 * @param T type of messages which are stored in the mailbox
 */
internal abstract class AbstractActor<T>(
    context: CoroutineContext = DefaultDispatcher,
    parent: Job? = null,
    start: CoroutineStart = CoroutineStart.LAZY,
    channelCapacity: Int = 16
) : ActorTraits() {

    internal val mailbox = Channel<T>(channelCapacity)
    public final override val job: Job
    private val onCloseInvoked = atomic(0)

    init {
        job = launch(context, start, parent) { actorLoop() }
        // Handler in case when actor was cancelled before start
        job.invokeOnCompletion {
            if (onCloseInvoked.compareAndSet(0, 1)) {
                onClose()
            }
        }
    }

    public override fun close() {
        mailbox.close()
    }

    public override fun cancel() {
        job.cancel()
        mailbox.cancel()
    }

    private suspend fun actorLoop() {
        try {
            onStart()
            for (message in mailbox) {
                onMessage(message)
            }
        } catch (e: Throwable) {
            handleCoroutineException(coroutineContext, e)
        } finally {
            mailbox.close()
            if (onCloseInvoked.compareAndSet(0, 1)) {
                onClose()
            }
        }
    }

    internal abstract suspend fun onMessage(message: T)
}
