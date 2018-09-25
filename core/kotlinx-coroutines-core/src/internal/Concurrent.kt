/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.internal

import java.lang.reflect.*
import java.util.*
import java.util.concurrent.*
import kotlin.concurrent.withLock as withLockJvm

internal actual fun <E> subscriberList(): SubscribersList<E> = CopyOnWriteArrayList<E>()

@Suppress("ACTUAL_WITHOUT_EXPECT")
internal actual typealias ReentrantLock = java.util.concurrent.locks.ReentrantLock

internal actual inline fun <T> ReentrantLock.withLock(action: () -> T) = this.withLockJvm(action)

internal actual fun <E> identitySet(expectedSize: Int): MutableSet<E> = Collections.newSetFromMap(IdentityHashMap(expectedSize))

private val REMOVE_FUTURE_ON_CANCEL: Method? = try {
    ScheduledThreadPoolExecutor::class.java.getMethod("setRemoveOnCancelPolicy", Boolean::class.java)
} catch (e: Throwable) {
    null
}

@Suppress("NAME_SHADOWING")
internal fun removeFutureOnCancel(executor: Executor): Boolean {
    try {
        val executor = executor as? ScheduledExecutorService ?: return false
        (REMOVE_FUTURE_ON_CANCEL ?: return false).invoke(executor, true)
        return true
    } catch (e: Throwable) {
        return true
    }
}
