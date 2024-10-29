package kotlinx.coroutines

/**
 * A runnable task for [CoroutineDispatcher.dispatch].
 *
 * Equivalent to the type `() -> Unit`.
 */
public actual fun interface Runnable {
    /**
     * @suppress
     */
    public actual fun run()
}
