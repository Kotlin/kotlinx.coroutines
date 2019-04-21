/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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
 */
private val handlers: List<CoroutineExceptionHandler> = CoroutineExceptionHandler::class.java.let { serviceClass ->
    ServiceLoader.load(serviceClass, serviceClass.classLoader).toList()
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
    currentThread.uncaughtExceptionHandler.uncaughtException(currentThread, exception)
}
