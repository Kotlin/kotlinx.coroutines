package kotlinx.coroutines.internal

import kotlinx.coroutines.*

internal actual fun propagateExceptionFinalResort(exception: Throwable) {
    // log exception
    console.error(exception.toString())
}