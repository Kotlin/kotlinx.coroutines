package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.native.*

private val lock = SynchronizedObject()

internal actual val platformExceptionHandlers: Collection<CoroutineExceptionHandler>
    get() = synchronized(lock) { platformExceptionHandlers_ }

private val platformExceptionHandlers_ = mutableSetOf<CoroutineExceptionHandler>()

internal actual fun ensurePlatformExceptionHandlerLoaded(callback: CoroutineExceptionHandler) {
    synchronized(lock) {
        platformExceptionHandlers_ += callback
    }
}

@OptIn(ExperimentalStdlibApi::class)
internal actual fun propagateExceptionFinalResort(exception: Throwable) {
    // log exception
    processUnhandledException(exception)
}

internal actual class DiagnosticCoroutineContextException actual constructor(context: CoroutineContext) :
    RuntimeException(context.toString())
