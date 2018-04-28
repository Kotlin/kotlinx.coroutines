package kotlinx.coroutines.experimental.internal

internal actual typealias ReentrantLock = NoOpLock

internal actual inline fun <T> ReentrantLock.withLock(action: () -> T) = action()

internal class NoOpLock {
    fun tryLock() = true
    fun unlock(): Unit {}
}

internal actual fun <E> subscriberList(): MutableList<E> = ArrayList()
