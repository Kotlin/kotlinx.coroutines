/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlin.coroutines.*

internal typealias OnUndeliveredElement<E> = (E) -> Unit

internal fun <E> OnUndeliveredElement<E>.callUndeliveredElementCatchingException(
    element: E,
    undeliveredElementException: UndeliveredElementException? = null
): UndeliveredElementException? {
    try {
        invoke(element)
    } catch (ex: Throwable) {
        // undeliveredElementException.cause !== ex is an optimization in case the same exception is thrown
        // over and over again by on OnUndeliveredElement
        if (undeliveredElementException != null && undeliveredElementException.cause !== ex) {
            undeliveredElementException.addSuppressedThrowable(ex)
        } else {
            return UndeliveredElementException("Exception in undelivered element handler for $element", ex)
        }
    }
    return undeliveredElementException
}

internal fun <E> OnUndeliveredElement<E>.callUndeliveredElement(element: E, context: CoroutineContext) {
    callUndeliveredElementCatchingException(element, null)?.let { ex ->
        handleCoroutineException(context, ex)
    }
}

internal fun <E> OnUndeliveredElement<E>.bindCancellationFun(element: E, context: CoroutineContext): (Throwable) -> Unit =
    { _: Throwable -> callUndeliveredElement(element, context) }

/**
 * Internal exception that is thrown when [OnUndeliveredElement] handler in
 * a [kotlinx.coroutines.channels.Channel] throws an exception.
 */
internal class UndeliveredElementException(message: String, cause: Throwable) : RuntimeException(message, cause)
