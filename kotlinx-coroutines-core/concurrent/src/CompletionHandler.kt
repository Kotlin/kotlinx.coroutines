package kotlinx.coroutines

import kotlinx.coroutines.internal.*

internal actual abstract class CompletionHandlerBase actual constructor() : LockFreeLinkedListNode(), CompletionHandler {
    actual abstract override fun invoke(cause: Throwable?)
}

internal actual inline val CompletionHandlerBase.asHandler: CompletionHandler get() = this

internal actual abstract class CancelHandlerBase actual constructor() : CompletionHandler {
    actual abstract override fun invoke(cause: Throwable?)
}

internal actual inline val CancelHandlerBase.asHandler: CompletionHandler get() = this

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun CompletionHandler.invokeIt(cause: Throwable?) = invoke(cause)
