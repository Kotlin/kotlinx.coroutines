package kotlinx.coroutines.experimental.actors

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*


/**
 * TODO
 */
public fun <T> actor(
    context: CoroutineContext = DefaultDispatcher,
    parent: ActorTraits? = null,
    start: CoroutineStart = CoroutineStart.LAZY,
    channelCapacity: Int = 16, onMessage: suspend MonoActor<T>.(T) -> Unit
): MonoActor<T> {
    return object : MonoActor<T>(context, parent?.job, start, channelCapacity) {
        override suspend fun receive(message: T) {
            onMessage(message)
        }
    }
}
