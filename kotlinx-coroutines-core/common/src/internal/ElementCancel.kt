package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlin.coroutines.*

internal typealias OnElementCancel<E> = (E) -> Unit

internal fun <E> OnElementCancel<E>.callElementCancelCatchingException(
    element: E,
    elementCancelException: ElementCancelException? = null
): ElementCancelException? {
    try {
        invoke(element)
    } catch (ex: Throwable) {
        if (elementCancelException != null) {
            elementCancelException.addSuppressedThrowable(ex)
        } else {
            return ElementCancelException("Exception in element cancellation for $element", ex)
        }
    }
    return elementCancelException
}

internal fun <E> OnElementCancel<E>.callElementCancel(resource: E, context: CoroutineContext) {
    callElementCancelCatchingException(resource, null)?.let { ex ->
        handleCoroutineException(context, ex)
    }
}

internal fun <E> OnElementCancel<E>.bindCancellationFun(element: E, context: CoroutineContext): (Throwable) -> Unit =
    { _: Throwable -> callElementCancel(element, context) }

internal class ElementCancelException(message: String, cause: Throwable) : RuntimeException(message, cause)
