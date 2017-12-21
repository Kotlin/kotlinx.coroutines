package kotlinx.coroutines.experimental

public expect suspend fun <T> withTimeout(time: Int, block: suspend CoroutineScope.() -> T): T

public expect suspend fun <T> withTimeoutOrNull(time: Int, block: suspend CoroutineScope.() -> T): T?

public expect class TimeoutCancellationException public constructor(message: String)
