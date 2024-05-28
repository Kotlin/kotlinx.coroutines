package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlin.coroutines.*

@InternalCoroutinesApi
public fun runTestCoroutine(context: CoroutineContext, block: suspend CoroutineScope.() -> Unit) {
    val newContext = GlobalScope.newCoroutineContext(context)
    val coroutine = object: AbstractCoroutine<Unit>(newContext, initParentJob = true, active = true) {}
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
    runEventLoop()
    check(coroutine.isCompleted) { "Coroutine $coroutine did not complete, but the system reached quiescence" }
    coroutine.getCompletionExceptionOrNull()?.let { throw it }
}