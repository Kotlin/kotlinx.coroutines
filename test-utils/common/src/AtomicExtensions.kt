@file:OptIn(ExperimentalAtomicApi::class)
@file:Suppress("NOTHING_TO_INLINE")
package kotlinx.coroutines.testing

import kotlin.concurrent.atomics.*

inline fun AtomicInt.increment() {
    val _ = fetchAndIncrement()
}

inline fun AtomicInt.decrement() {
    val _ = fetchAndDecrement()
}

inline fun AtomicLong.increment() {
    val _ = fetchAndIncrement()
}

inline fun AtomicLong.decrement() {
    val _ = fetchAndDecrement()
}

