package kotlinx.coroutines.internal

import java.lang.reflect.*
import java.util.*
import java.util.concurrent.*
import kotlin.concurrent.withLock as withLockJvm

@Suppress("ACTUAL_WITHOUT_EXPECT")
internal actual typealias ReentrantLock = java.util.concurrent.locks.ReentrantLock

internal actual inline fun <T> ReentrantLock.withLock(action: () -> T) = this.withLockJvm(action)

@Suppress("ACTUAL_WITHOUT_EXPECT") // Visibility
internal actual typealias WorkaroundAtomicReference<T> = java.util.concurrent.atomic.AtomicReference<T>

@Suppress("NOTHING_TO_INLINE") // So that R8 can completely remove ConcurrentKt class
internal actual inline fun <E> identitySet(expectedSize: Int): MutableSet<E> =
    Collections.newSetFromMap(IdentityHashMap(expectedSize))

private val REMOVE_FUTURE_ON_CANCEL: Method? = try {
    ScheduledThreadPoolExecutor::class.java.getMethod("setRemoveOnCancelPolicy", Boolean::class.java)
} catch (e: Throwable) {
    null
}

@Suppress("NAME_SHADOWING")
internal fun removeFutureOnCancel(executor: Executor): Boolean {
    try {
        val executor = executor as? ScheduledThreadPoolExecutor ?: return false
        (REMOVE_FUTURE_ON_CANCEL ?: return false).invoke(executor, true)
        return true
    } catch (e: Throwable) {
        return false // failed to setRemoveOnCancelPolicy, assume it does not removes future on cancel
    }
}
