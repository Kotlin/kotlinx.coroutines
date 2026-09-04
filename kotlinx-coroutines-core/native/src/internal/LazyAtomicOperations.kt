package kotlinx.coroutines.internal

import kotlin.concurrent.atomics.AtomicArray
import kotlin.concurrent.atomics.ExperimentalAtomicApi

@ExperimentalAtomicApi
@Suppress("NOTHING_TO_INLINE")
internal actual inline fun <T> AtomicArray<T>.storeLazyAt(index: Int, value: T) = storeAt(index, value)
