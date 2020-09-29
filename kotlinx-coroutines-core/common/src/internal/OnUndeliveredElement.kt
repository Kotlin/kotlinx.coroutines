/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlin.coroutines.*

internal typealias OnUndeliveredElement<E> = (E) -> Unit

internal fun <E> OnUndeliveredElement<E>.callElementUndeliveredCatchingException(
    element: E,
    elementCancelException: UndeliveredElementException? = null
): UndeliveredElementException? {
    try {
        invoke(element)
    } catch (ex: Throwable) {
        if (elementCancelException != null) {
            elementCancelException.addSuppressedThrowable(ex)
        } else {
            return UndeliveredElementException("Exception in element cancellation for $element", ex)
        }
    }
    return elementCancelException
}

internal fun <E> OnUndeliveredElement<E>.callElementUndelivered(resource: E, context: CoroutineContext) {
    callElementUndeliveredCatchingException(resource, null)?.let { ex ->
        handleCoroutineException(context, ex)
    }
}

internal fun <E> OnUndeliveredElement<E>.bindCancellationFun(element: E, context: CoroutineContext): (Throwable) -> Unit =
    { _: Throwable -> callElementUndelivered(element, context) }

/**
 * Internal exception that is thrown when [OnUndeliveredElement] handler in
 * a [kotlinx.coroutines.channels.Channel] throws an exception.
 */
internal class UndeliveredElementException(message: String, cause: Throwable) : RuntimeException(message, cause)
