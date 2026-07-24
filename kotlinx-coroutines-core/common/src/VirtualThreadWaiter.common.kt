package kotlinx.coroutines

import kotlin.coroutines.CoroutineContext

/** Blocks and wakes the virtual thread that owns a coroutine. */
internal expect class VirtualThreadWaiter(context: CoroutineContext) {
    fun await()
    fun signal()
}
