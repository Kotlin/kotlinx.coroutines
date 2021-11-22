/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

/**
 * Special kind of list intended to be used as collection of subscribers in `ArrayBroadcastChannel`
 * On JVM it's CopyOnWriteList and on JS it's MutableList.
 *
 * Note that this alias is intentionally not named as CopyOnWriteList to avoid accidental misusage outside of the ArrayBroadcastChannel
 */
internal typealias SubscribersList<E> = MutableList<E>

@Deprecated(message = "Implementation of this primitive is tailored to specific ArrayBroadcastChannel usages on K/N " +
    "and K/JS platforms and it is unsafe to use it anywhere else")
internal expect fun <E> subscriberList(): SubscribersList<E>

internal expect class ReentrantLock() {
    fun tryLock(): Boolean
    fun unlock(): Unit
}

internal expect inline fun <T> ReentrantLock.withLock(action: () -> T): T

internal expect fun <E> identitySet(expectedSize: Int): MutableSet<E>
