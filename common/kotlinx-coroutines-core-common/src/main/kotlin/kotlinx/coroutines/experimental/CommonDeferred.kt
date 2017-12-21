package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.CoroutineContext

public expect interface Deferred<out T> : Job {
    public val isCompletedExceptionally: Boolean
    public suspend fun await(): T
    public fun getCompleted(): T
    public fun getCompletionExceptionOrNull(): Throwable?
}

@Suppress("EXPECTED_DECLARATION_WITH_DEFAULT_PARAMETER")
public expect fun <T> async(
    context: CoroutineContext = DefaultDispatcher,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    parent: Job? = null,
    block: suspend CoroutineScope.() -> T
): Deferred<T>