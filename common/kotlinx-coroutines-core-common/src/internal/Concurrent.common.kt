/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

/**
 * Special kind of list intended to be used as collection of subscribers in `ArrayBroadcastChannel`
 * On JVM it's CopyOnWriteList and on JS it's MutableList.
 *
 * Note that this alias is intentionally not named as CopyOnWriteList to avoid accidental misusage outside of ArrayBroadcastChannel
 */
internal typealias SubscribersList<E> = MutableList<E>

internal expect fun <E> subscriberList(): SubscribersList<E>

internal expect class ReentrantLock() {
    fun tryLock(): Boolean
    fun unlock(): Unit
}

internal expect inline fun <T> ReentrantLock.withLock(action: () -> T): T

internal expect fun <E> identitySet(expectedSize: Int): MutableSet<E>

@ExperimentalMultiplatform
@OptionalExpectation
internal expect annotation class SharedImmutable()
