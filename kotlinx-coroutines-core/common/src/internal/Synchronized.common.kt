/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlin.contracts.*

/**
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public expect open class SynchronizedObject() // marker abstract class

/**
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public expect inline fun <T> synchronizedImpl(lock: SynchronizedObject, block: () -> T): T

/**
 * @suppress **This an internal API and should not be used from general code.**
 */
@OptIn(ExperimentalContracts::class)
@InternalCoroutinesApi
public inline fun <T> synchronized(lock: SynchronizedObject, block: () -> T): T {
    contract {
        callsInPlace(block, InvocationKind.EXACTLY_ONCE)
    }
    return synchronizedImpl(lock, block)
}
