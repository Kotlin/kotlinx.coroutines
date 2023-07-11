/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlin.coroutines.*

/**
 * The list of globally installed [CoroutineExceptionHandler] instances that will be notified of any exceptions that
 * were not processed in any other manner.
 */
internal expect val platformExceptionHandlers: Collection<CoroutineExceptionHandler>

/**
 * Ensures that the given [callback] is present in the [platformExceptionHandlers] list.
 */
internal expect fun ensurePlatformExceptionHandlerLoaded(callback: CoroutineExceptionHandler)

/**
 * The platform-dependent global exception handler, used so that the exception is logged at least *somewhere*.
 */
internal expect fun propagateExceptionFinalResort(exception: Throwable)

/**
 * Deal with exceptions that happened in coroutines and weren't programmatically dealt with.
 *
 * First, it notifies every [CoroutineExceptionHandler] in the [platformExceptionHandlers] list.
 * If one of them throws [ExceptionSuccessfullyProcessed], it means that that handler believes that the exception was
 * dealt with sufficiently well and doesn't need any further processing.
 * Otherwise, the platform-dependent global exception handler is also invoked.
 */
internal fun handleUncaughtCoroutineException(context: CoroutineContext, exception: Throwable) {
    // use additional extension handlers
    for (handler in platformExceptionHandlers) {
        try {
            handler.handleException(context, exception)
        } catch (_: ExceptionSuccessfullyProcessed) {
            return
        } catch (t: Throwable) {
            propagateExceptionFinalResort(handlerException(exception, t))
        }
    }

    try {
        exception.addSuppressed(DiagnosticCoroutineContextException(context))
    } catch (e: Throwable) {
        // addSuppressed is never user-defined and cannot normally throw with the only exception being OOM
        // we do ignore that just in case to definitely deliver the exception
    }
    propagateExceptionFinalResort(exception)
}

/**
 * Private exception that is added to suppressed exceptions of the original exception
 * when it is reported to the last-ditch current thread 'uncaughtExceptionHandler'.
 *
 * The purpose of this exception is to add an otherwise inaccessible diagnostic information and to
 * be able to poke the context of the failing coroutine in the debugger.
 */
internal expect class DiagnosticCoroutineContextException(context: CoroutineContext) : RuntimeException

/**
 * A dummy exception that signifies that the exception was successfully processed by the handler and no further
 * action is required.
 *
 * Would be nicer if [CoroutineExceptionHandler] could return a boolean, but that would be a breaking change.
 * For now, we will take solace in knowledge that such exceptions are exceedingly rare, even rarer than globally
 * uncaught exceptions in general.
 */
internal object ExceptionSuccessfullyProcessed : Exception()
