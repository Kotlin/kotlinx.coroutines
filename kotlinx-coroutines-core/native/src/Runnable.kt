package kotlinx.coroutines

/**
 * A runnable task for [CoroutineDispatcher.dispatch].
 */
public actual interface Runnable {
    /**
     * @suppress
     */
    public actual fun run()
}

/**
 * Creates [Runnable] task instance.
 */
@Suppress("FunctionName")
public actual inline fun Runnable(crossinline block: () -> Unit): Runnable =
    object : Runnable {
        override fun run() {
            block()
        }
    }
