/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

internal actual typealias ReentrantLock = NoOpLock

internal actual inline fun <T> ReentrantLock.withLock(action: () -> T) = action()

internal class NoOpLock {
    fun tryLock() = true
    fun unlock(): Unit {}
}

internal actual fun <E> subscriberList(): MutableList<E> = CopyOnWriteList<E>()

internal actual fun <E> identitySet(expectedSize: Int): MutableSet<E> = HashSet()
