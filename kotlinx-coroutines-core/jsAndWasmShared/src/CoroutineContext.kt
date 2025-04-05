package kotlinx.coroutines

import kotlin.coroutines.*

@PublishedApi // Used from kotlinx-coroutines-test via suppress, not part of ABI
internal actual val DefaultDelay: Delay
    get() = Dispatchers.Default as Delay

// No debugging facilities on Wasm and JS
internal actual fun Continuation<*>.toDebugString(): String = toString()
internal actual val CoroutineContext.coroutineName: String? get() = null // not supported on Wasm and JS
internal actual fun wrapContextWithDebug(context: CoroutineContext): CoroutineContext = context
