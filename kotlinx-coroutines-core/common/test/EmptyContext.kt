package kotlinx.coroutines

import kotlinx.coroutines.intrinsics.*
import kotlin.coroutines.*

suspend fun <T> withEmptyContext(block: suspend () -> T): T = suspendCoroutine { cont ->
    block.startCoroutineUnintercepted(Continuation(EmptyCoroutineContext) { cont.resumeWith(it) })
}
