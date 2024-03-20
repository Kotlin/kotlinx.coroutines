package kotlinx.coroutines.internal

internal actual typealias ReentrantLock = NoOpLock

internal actual inline fun <T> ReentrantLock.withLock(action: () -> T) = action()

internal class NoOpLock {
    fun tryLock() = true
    fun unlock(): Unit {}
}

internal actual fun <E> identitySet(expectedSize: Int): MutableSet<E> = HashSet(expectedSize)

internal actual class WorkaroundAtomicReference<V> actual constructor(private var value: V) {

    public actual fun get(): V = value

    public actual fun set(value: V) {
        this.value = value
    }

    public actual fun getAndSet(value: V): V {
        val prev = this.value
        this.value = value
        return prev
    }

    public actual fun compareAndSet(expected: V, value: V): Boolean {
        if (this.value === expected) {
            this.value = value
            return true
        }
        return false
    }
}
