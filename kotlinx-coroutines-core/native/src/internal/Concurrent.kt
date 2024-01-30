package kotlinx.coroutines.internal

import kotlinx.atomicfu.*
import kotlinx.cinterop.*
import kotlinx.atomicfu.locks.withLock as withLock2

@Suppress("ACTUAL_WITHOUT_EXPECT")
internal actual typealias ReentrantLock = kotlinx.atomicfu.locks.SynchronizedObject

internal actual inline fun <T> ReentrantLock.withLock(action: () -> T): T = this.withLock2(action)

internal actual fun <E> identitySet(expectedSize: Int): MutableSet<E> = HashSet()

@Suppress("ACTUAL_WITHOUT_EXPECT") // This suppress can be removed in 2.0: KT-59355
internal actual typealias BenignDataRace = kotlin.concurrent.Volatile
