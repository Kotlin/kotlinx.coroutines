package kotlinx.coroutines.internal

import java.util.*
import kotlin.concurrent.withLock as withLockJvm

@Suppress("ACTUAL_WITHOUT_EXPECT")
internal actual typealias ReentrantLock = java.util.concurrent.locks.ReentrantLock

internal actual inline fun <T> ReentrantLock.withLock(action: () -> T) = this.withLockJvm(action)

@Suppress("ACTUAL_WITHOUT_EXPECT") // Visibility
internal actual typealias WorkaroundAtomicReference<T> = java.util.concurrent.atomic.AtomicReference<T>

// BenignDataRace is OptionalExpectation and doesn't have to be here
// but then IC breaks. See KT-66317
@Retention(AnnotationRetention.SOURCE)
@Target(AnnotationTarget.FIELD)
internal actual annotation class BenignDataRace()

@Suppress("NOTHING_TO_INLINE") // So that R8 can completely remove ConcurrentKt class
internal actual inline fun <E> identitySet(expectedSize: Int): MutableSet<E> =
    Collections.newSetFromMap(IdentityHashMap(expectedSize))
