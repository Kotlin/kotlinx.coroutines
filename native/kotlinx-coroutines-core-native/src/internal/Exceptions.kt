package kotlinx.coroutines.experimental.internal

import kotlin.coroutines.experimental.*

internal actual fun <E: Throwable> recoverStackTrace(exception: E, continuation: Continuation<*>): E = exception
internal actual fun <E: Throwable> recoverStackTrace(exception: E): E = exception
