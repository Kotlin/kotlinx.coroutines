/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

internal expect class ReentrantLock() {
    fun tryLock(): Boolean
    fun unlock()
}

internal expect inline fun <T> ReentrantLock.withLock(action: () -> T): T

internal expect fun <E> identitySet(expectedSize: Int): MutableSet<E>
