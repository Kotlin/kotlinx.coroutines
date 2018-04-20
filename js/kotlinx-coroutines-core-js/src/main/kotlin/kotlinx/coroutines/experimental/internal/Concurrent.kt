package kotlinx.coroutines.experimental.internal

actual typealias ReentrantLock = NoOpLock

actual inline fun <T> ReentrantLock.withLock(action: () -> T) = action()

public class NoOpLock {
    fun tryLock() = true
    fun unlock(): Unit {}
}

actual fun <E> subscriberList(): MutableList<E> = ArrayList()
