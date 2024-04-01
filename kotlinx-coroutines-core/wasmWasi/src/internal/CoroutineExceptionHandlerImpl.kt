package kotlinx.coroutines.internal

internal actual fun propagateExceptionFinalResort(exception: Throwable) {
    println(exception.toString())
}