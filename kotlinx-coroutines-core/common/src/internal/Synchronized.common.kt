/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.coroutines.*

/**
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public expect open class SynchronizedObject() // marker abstract class

/**
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public expect inline fun <T> synchronized(lock: SynchronizedObject, block: () -> T): T