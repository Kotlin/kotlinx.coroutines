package kotlinx.coroutines.internal

import kotlinx.atomicfu.*
import kotlinx.cinterop.*
import kotlinx.atomicfu.locks.withLock as withLock2

internal actual typealias ReentrantLock = kotlinx.atomicfu.locks.SynchronizedObject

internal actual inline fun <T> ReentrantLock.withLock(action: () -> T): T = this.withLock2(action)

internal actual fun <E> identitySet(expectedSize: Int): MutableSet<E> = HashSet()

internal actual typealias BenignDataRace = kotlin.concurrent.Volatile

internal actual class WorkaroundAtomicReference<V> actual constructor(value: V) {

    private val nativeAtomic = kotlin.concurrent.AtomicReference<V>(value)

    public actual fun get(): V= nativeAtomic.value

    public actual fun set(value: V) {
        nativeAtomic.value = value
    }

    public actual fun getAndSet(value: V): V = nativeAtomic.getAndSet(value)

    public actual fun compareAndSet(expected: V, value: V): Boolean = nativeAtomic.compareAndSet(expected, value)
}
