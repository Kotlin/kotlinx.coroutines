package kotlinx.coroutines.internal

import kotlinx.coroutines.*

/** @suppress */
@InternalCoroutinesApi // Emulating DI for Kotlin object's
public interface MainDispatcherFactory {
    public val loadPriority: Int // higher priority wins

    /**
     * Creates the main dispatcher. [allFactories] parameter contains all factories found by service loader.
     * This method is not guaranteed to be idempotent.
     *
     * It is required that this method fails with an exception instead of returning an instance that doesn't work
     * correctly as a [Delay].
     * The reason for this is that, on the JVM, [DefaultDelay] will use [Dispatchers.Main] for most delays by default
     * if this method returns an instance without throwing.
     */
    public fun createDispatcher(allFactories: List<MainDispatcherFactory>): MainCoroutineDispatcher

    /**
     * Hint used along with error message when the factory failed to create a dispatcher.
     */
    public fun hintOnError(): String? = null
}
