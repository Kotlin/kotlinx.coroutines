/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.internal

import java.util.*
import java.util.concurrent.*
import kotlin.concurrent.withLock as withLockJvm

internal actual fun <E> subscriberList(): SubscribersList<E> = CopyOnWriteArrayList<E>()

@Suppress("ACTUAL_WITHOUT_EXPECT")
internal actual typealias ReentrantLock = java.util.concurrent.locks.ReentrantLock

internal actual inline fun <T> ReentrantLock.withLock(action: () -> T) = this.withLockJvm(action)

internal actual fun <E> identitySet(expectedSize: Int): MutableSet<E> = Collections.newSetFromMap(IdentityHashMap(expectedSize))
