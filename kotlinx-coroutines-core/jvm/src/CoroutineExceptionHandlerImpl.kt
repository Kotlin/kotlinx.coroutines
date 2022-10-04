/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import java.util.*
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
private val handlers: List<CoroutineExceptionHandler> = ServiceLoader.load(
        CoroutineExceptionHandler::class.java,
        CoroutineExceptionHandler::class.java.classLoader
).iterator().asSequence().toList()

/**
 * Private exception without stacktrace that is added to suppressed exceptions of the original exception
 * when it is reported to the last-ditch current thread 'uncaughtExceptionHandler'.
 *
 * The purpose of this exception is to add an otherwise inaccessible diagnostic information and to
 * be able to poke the failing coroutine context in the debugger.
 */
private class DiagnosticCoroutineContextException(@Transient private val context: CoroutineContext) : RuntimeException() {
    override fun getLocalizedMessage(): String {
        return context.toString()
    }

    override fun fillInStackTrace(): Throwable {
        // Prevent Android <= 6.0 bug, #1866
        stackTrace = emptyArray()
        return this
    }
}

internal actual fun handleCoroutineExceptionImpl(context: CoroutineContext, exception: Throwable) {
    // use additional extension handlers
    for (handler in handlers) {
        try {
            handler.handleException(context, exception)
        } catch (t: Throwable) {
            // Use thread's handler if custom handler failed to handle exception
            val currentThread = Thread.currentThread()
            currentThread.uncaughtExceptionHandler.uncaughtException(currentThread, handlerException(exception, t))
        }
    }

    // use thread's handler
    val currentThread = Thread.currentThread()
    // addSuppressed is never user-defined and cannot normally throw with the only exception being OOM
    // we do ignore that just in case to definitely deliver the exception
    runCatching { exception.addSuppressed(DiagnosticCoroutineContextException(context)) }
    currentThread.uncaughtExceptionHandler.uncaughtException(currentThread, exception)
}
