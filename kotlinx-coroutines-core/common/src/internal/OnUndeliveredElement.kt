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
            undeliveredElementException.addSuppressed(ex)
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

/**
 * Internal exception that is thrown when [OnUndeliveredElement] handler in
 * a [kotlinx.coroutines.channels.Channel] throws an exception.
 */
internal class UndeliveredElementException(message: String, cause: Throwable) : RuntimeException(message, cause)
