package kotlinx.coroutines

/**
 * A runnable task for [CoroutineDispatcher.dispatch].
 *
 * It is a typealias for [java.lang.Runnable], which is widely used in Java APIs.
 * This makes it possible to directly pass the argument of [CoroutineDispatcher.dispatch]
 * to the underlying Java implementation without any additional wrapping.
 */
public actual typealias Runnable = java.lang.Runnable
