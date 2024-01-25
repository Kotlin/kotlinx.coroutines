package kotlinx.coroutines.internal

import kotlinx.coroutines.*

/**
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public actual typealias SynchronizedObject = Any

/**
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public actual inline fun <T> synchronizedImpl(lock: SynchronizedObject, block: () -> T): T =
    kotlin.synchronized(lock, block)
