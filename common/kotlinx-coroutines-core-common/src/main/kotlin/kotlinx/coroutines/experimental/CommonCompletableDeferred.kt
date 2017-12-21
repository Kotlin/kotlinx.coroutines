package kotlinx.coroutines.experimental

public expect interface CompletableDeferred<T> : Deferred<T> {
    public fun complete(value: T): Boolean
    public fun completeExceptionally(exception: Throwable): Boolean
}

@Suppress("FunctionName", "EXPECTED_DECLARATION_WITH_DEFAULT_PARAMETER")
public expect fun <T> CompletableDeferred(parent: Job? = null): CompletableDeferred<T>

@Suppress("FunctionName", "EXPECTED_DECLARATION_WITH_DEFAULT_PARAMETER")
public expect fun <T> CompletableDeferred(value: T): CompletableDeferred<T>
