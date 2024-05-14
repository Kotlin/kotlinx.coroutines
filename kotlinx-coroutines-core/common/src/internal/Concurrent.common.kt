package kotlinx.coroutines.internal

internal expect class ReentrantLock() {
    fun tryLock(): Boolean
    fun unlock()
}

internal expect inline fun <T> ReentrantLock.withLock(action: () -> T): T

internal expect fun <E> identitySet(expectedSize: Int): MutableSet<E>

/**
 * Annotation indicating that the marked property is the subject of benign data race.
 * LLVM does not support this notion, so on K/N platforms we alias it into `@Volatile` to prevent potential OoTA.
 *
 * The purpose of this annotation is not to save an extra-volatile on JVM platform, but rather to explicitly emphasize
 * that data-race is benign.
 */
@OptionalExpectation
@Target(AnnotationTarget.FIELD)
internal expect annotation class BenignDataRace()

// Used **only** as a workaround for #3820 in StateFlow. Do not use anywhere else
internal expect class WorkaroundAtomicReference<V>(value: V) {
    public fun get(): V
    public fun set(value: V)
    public fun getAndSet(value: V): V
    public fun compareAndSet(expected: V, value: V): Boolean
}

@Suppress("UNUSED_PARAMETER", "EXTENSION_SHADOWED_BY_MEMBER")
internal var <T> WorkaroundAtomicReference<T>.value: T
    get() = this.get()
    set(value) = this.set(value)

internal inline fun <T> WorkaroundAtomicReference<T>.loop(action: WorkaroundAtomicReference<T>.(value: T) -> Unit) {
    while (true) {
        action(value)
    }
}
