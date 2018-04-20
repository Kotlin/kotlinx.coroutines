package kotlinx.coroutines.experimental.internal

import java.util.concurrent.*
import kotlin.concurrent.withLock as withLockJvm

actual fun <E> subscriberList(): MutableList<E> = CopyOnWriteArrayList<E>()

actual typealias ReentrantLock = java.util.concurrent.locks.ReentrantLock

actual inline fun <T> ReentrantLock.withLock(action: () -> T) = this.withLockJvm(action)
