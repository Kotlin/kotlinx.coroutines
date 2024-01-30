package kotlinx.coroutines.internal

import kotlinx.cinterop.*
import kotlinx.coroutines.*
import kotlinx.atomicfu.locks.withLock as withLock2

/**
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public actual typealias SynchronizedObject = kotlinx.atomicfu.locks.SynchronizedObject

/**
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public actual inline fun <T> synchronizedImpl(lock: SynchronizedObject, block: () -> T): T = lock.withLock2(block)
