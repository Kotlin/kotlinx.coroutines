package kotlinx.coroutines

/**
 * A runnable task for [CoroutineDispatcher.dispatch].
 */
public expect interface Runnable {
    /**
     * @suppress
     */
    public fun run()
}

/**
 * Creates [Runnable] task instance.
 */
@Suppress("FunctionName")
public expect inline fun Runnable(crossinline block: () -> Unit): Runnable
