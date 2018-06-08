package kotlinx.coroutines.experimental.actors

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlin.coroutines.experimental.*


/**
 * Launches a new [MonoActor] with given [block] as [message handler][MonoActor.receive]
 */
public fun <T> actor(
    context: CoroutineContext = DefaultDispatcher,
    parent: ActorTraits? = null,
    start: CoroutineStart = CoroutineStart.LAZY,
    channelCapacity: Int = 16, block: suspend MonoActor<T>.(T) -> Unit
): MonoActor<T> {
    return object : MonoActor<T>(context, parent?.job, start, channelCapacity) {
        override suspend fun receive(message: T) {
            block(message)
        }
    }
}

/**
 * Launches a new [MonoActor] with given [block] as [message handler][MonoActor.receive]
 */
public fun <T> actor(
    context: CoroutineContext = DefaultDispatcher,
    parent: Job,
    start: CoroutineStart = CoroutineStart.LAZY,
    channelCapacity: Int = 16, block: suspend MonoActor<T>.(T) -> Unit
): MonoActor<T> {
    return object : MonoActor<T>(context, parent, start, channelCapacity) {
        override suspend fun receive(message: T) {
            block(message)
        }
    }
}
