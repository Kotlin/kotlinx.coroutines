package kotlinx.coroutines.experimental.internal

import java.util.concurrent.*
import kotlin.concurrent.withLock as withLockJvm

internal actual fun <E> subscriberList(): MutableList<E> = CopyOnWriteArrayList<E>()

@Suppress("ACTUAL_WITHOUT_EXPECT")
internal actual typealias ReentrantLock = java.util.concurrent.locks.ReentrantLock

internal actual inline fun <T> ReentrantLock.withLock(action: () -> T) = this.withLockJvm(action)
