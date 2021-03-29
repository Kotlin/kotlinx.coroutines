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
    currentThread.uncaughtExceptionHandler.uncaughtException(currentThread, exception)
}
