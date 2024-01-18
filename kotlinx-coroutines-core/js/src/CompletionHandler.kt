package kotlinx.coroutines

import kotlinx.coroutines.internal.*

internal actual abstract class CompletionHandlerBase : LinkedListNode() {
    @JsName("invoke")
    actual abstract fun invoke(cause: Throwable?)
}

@Suppress("UnsafeCastFromDynamic")
internal actual inline val CompletionHandlerBase.asHandler: CompletionHandler get() = asDynamic()

internal actual abstract class CancelHandlerBase {
    @JsName("invoke")
    actual abstract fun invoke(cause: Throwable?)
}

@Suppress("UnsafeCastFromDynamic")
internal actual inline val CancelHandlerBase.asHandler: CompletionHandler get() = asDynamic()

internal actual fun CompletionHandler.invokeIt(cause: Throwable?) {
    when(jsTypeOf(this)) {
        "function" -> invoke(cause)
        else -> asDynamic().invoke(cause)
    }
}
