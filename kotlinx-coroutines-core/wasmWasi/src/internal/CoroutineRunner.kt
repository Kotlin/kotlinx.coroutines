package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlin.coroutines.*

@InternalCoroutinesApi
public fun runTestCoroutine(context: CoroutineContext, block: suspend CoroutineScope.() -> Unit) {
    val newContext = GlobalScope.newCoroutineContext(context)
    val coroutine = object: AbstractCoroutine<Unit>(newContext, true, true) {}
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
    runEventLoop()
    if (coroutine.isCancelled) throw coroutine.getCancellationException().let { it.cause ?: it }
}