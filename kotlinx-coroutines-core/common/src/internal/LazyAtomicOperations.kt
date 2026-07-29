package kotlinx.coroutines.internal

import kotlin.concurrent.atomics.AtomicArray
import kotlin.concurrent.atomics.ExperimentalAtomicApi

@ExperimentalAtomicApi
internal expect inline fun <T> AtomicArray<T>.storeLazyAt(index: Int, value: T)
