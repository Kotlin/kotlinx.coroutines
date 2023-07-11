/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import java.util.*
import kotlinx.coroutines.*
import kotlin.coroutines.*

/**
 * A list of globally installed [CoroutineExceptionHandler] instances.
 *
 * Note that Android may have dummy [Thread.contextClassLoader] which is used by one-argument [ServiceLoader.load] function,
 * see (https://stackoverflow.com/questions/13407006/android-class-loader-may-fail-for-processes-that-host-multiple-applications).
 * So here we explicitly use two-argument `load` with a class-loader of [CoroutineExceptionHandler] class.
 *
 * We are explicitly using the `ServiceLoader.load(MyClass::class.java, MyClass::class.java.classLoader).iterator()`
 * form of the ServiceLoader call to enable R8 optimization when compiled on Android.
 */
internal actual val platformExceptionHandlers: Collection<CoroutineExceptionHandler> = ServiceLoader.load(
    CoroutineExceptionHandler::class.java,
    CoroutineExceptionHandler::class.java.classLoader
).iterator().asSequence().toList()

internal actual fun ensurePlatformExceptionHandlerLoaded(callback: CoroutineExceptionHandler) {
    // we use JVM's mechanism of ServiceLoader, so this should be a no-op on JVM.
    // The only thing we do is make sure that the ServiceLoader did work correctly.
    check(callback in platformExceptionHandlers) { "Exception handler was not found via a ServiceLoader" }
}

internal actual fun propagateExceptionFinalResort(exception: Throwable) {
    // use the thread's handler
    val currentThread = Thread.currentThread()
    currentThread.uncaughtExceptionHandler.uncaughtException(currentThread, exception)
}

// This implementation doesn't store a stacktrace, which is good because a stacktrace doesn't make sense for this.
internal actual class DiagnosticCoroutineContextException actual constructor(@Transient private val context: CoroutineContext) : RuntimeException() {
    override fun getLocalizedMessage(): String {
        return context.toString()
    }

    override fun fillInStackTrace(): Throwable {
        // Prevent Android <= 6.0 bug, #1866
        stackTrace = emptyArray()
        return this
    }
}
