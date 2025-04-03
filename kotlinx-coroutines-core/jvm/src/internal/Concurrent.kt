package kotlinx.coroutines.internal

import java.lang.reflect.Method
import java.util.*
import java.util.concurrent.Executor
import java.util.concurrent.ScheduledThreadPoolExecutor
import kotlin.concurrent.withLock as withLockJvm

internal actual typealias ReentrantLock = java.util.concurrent.locks.ReentrantLock

internal actual inline fun <T> ReentrantLock.withLock(action: () -> T) = this.withLockJvm(action)

internal actual typealias WorkaroundAtomicReference<T> = java.util.concurrent.atomic.AtomicReference<T>

// BenignDataRace is OptionalExpectation and doesn't have to be here
// but then IC breaks. See KT-66317
@Retention(AnnotationRetention.SOURCE)
@Target(AnnotationTarget.FIELD)
internal actual annotation class BenignDataRace()

@Suppress("NOTHING_TO_INLINE") // So that R8 can completely remove ConcurrentKt class
internal actual inline fun <E> identitySet(expectedSize: Int): MutableSet<E> =
    Collections.newSetFromMap(IdentityHashMap(expectedSize))

private val REMOVE_FUTURE_ON_CANCEL: Method? = try {
    ScheduledThreadPoolExecutor::class.java.getMethod("setRemoveOnCancelPolicy", Boolean::class.java)
} catch (_: Throwable) {
    null
}

/* We can not simply call `setRemoveOnCancelPolicy`, even though the code would compile and tests would pass,
 * because older Android versions don't support it. */
@Suppress("NAME_SHADOWING")
internal fun removeFutureOnCancel(executor: Executor): Boolean {
    try {
        val executor = executor as? ScheduledThreadPoolExecutor ?: return false
        (REMOVE_FUTURE_ON_CANCEL ?: return false).invoke(executor, true)
        return true
    } catch (_: Throwable) {
        return false // failed to setRemoveOnCancelPolicy, assume it does not remove the future on cancel
    }
}
