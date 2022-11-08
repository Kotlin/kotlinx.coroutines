/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

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
public actual inline fun <T> synchronized(lock: SynchronizedObject, block: () -> T): T = lock.withLock2(block)
