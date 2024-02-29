package kotlinx.coroutines.internal

internal actual typealias ReentrantLock = NoOpLock

internal actual inline fun <T> ReentrantLock.withLock(action: () -> T) = action()

internal class NoOpLock {
    fun tryLock() = true
    fun unlock(): Unit {}
}

internal actual fun <E> identitySet(expectedSize: Int): MutableSet<E> = HashSet(expectedSize)

internal actual class WorkaroundAtomicReference<T> actual constructor(private var value: T) {

    public actual fun get(): T = value

    public actual fun set(value: T) {
        this.value = value
    }

    public actual fun getAndSet(value: T): T {
        val prev = this.value
        this.value = value
        return prev
    }

    public actual fun compareAndSet(expected: T, value: T): Boolean {
        if (this.value === expected) {
            this.value = value
            return true
        }
        return false
    }
}
