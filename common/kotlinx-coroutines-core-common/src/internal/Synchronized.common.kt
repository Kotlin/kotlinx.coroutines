/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.internal

internal expect open class SynchronizedObject() // marker abstract class

@PublishedApi
internal expect inline fun <T> synchronized(lock: SynchronizedObject, block: () -> T): T