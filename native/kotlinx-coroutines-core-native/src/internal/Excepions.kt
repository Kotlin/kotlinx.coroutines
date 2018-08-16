package kotlinx.coroutines.experimental.internal

internal actual fun <E: Throwable> augmentException(e: E): E = e
