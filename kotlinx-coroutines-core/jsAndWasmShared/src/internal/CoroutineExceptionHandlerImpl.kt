package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlin.coroutines.*

private val platformExceptionHandlers_ = mutableSetOf<CoroutineExceptionHandler>()

internal actual val platformExceptionHandlers: Collection<CoroutineExceptionHandler>
    get() = platformExceptionHandlers_

internal actual fun ensurePlatformExceptionHandlerLoaded(callback: CoroutineExceptionHandler) {
    platformExceptionHandlers_ += callback
}

internal actual class DiagnosticCoroutineContextException actual constructor(context: CoroutineContext) :
    RuntimeException(context.toString())

