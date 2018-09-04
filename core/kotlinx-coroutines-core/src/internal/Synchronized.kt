/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.internal

@Suppress("ACTUAL_WITHOUT_EXPECT") // visibility
internal actual typealias SynchronizedObject = Any

@PublishedApi
internal actual inline fun <T> synchronized(lock: SynchronizedObject, block: () -> T): T =
    kotlin.synchronized(lock, block)