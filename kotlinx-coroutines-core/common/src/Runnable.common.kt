package kotlinx.coroutines

/**
 * A runnable task for [CoroutineDispatcher.dispatch].
 *
 * It is equivalent to the type `() -> Unit`, but on the JVM, it is represented as a `java.lang.Runnable`,
 * making it easier to wrap the interfaces that expect `java.lang.Runnable` into a [CoroutineDispatcher].
 */
public expect fun interface Runnable {
    /**
     * @suppress
     */
    public fun run()
}
