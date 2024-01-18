package kotlinx.coroutines

/**
 * A runnable task for [CoroutineDispatcher.dispatch].
 */
public actual typealias Runnable = java.lang.Runnable

/**
 * Creates [Runnable] task instance.
 */
@Suppress("FunctionName")
public actual inline fun Runnable(crossinline block: () -> Unit): Runnable =
    java.lang.Runnable { block() }
