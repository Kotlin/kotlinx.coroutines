package kotlinx.coroutines.internal

import kotlin.concurrent.atomics.AtomicArray
import kotlin.concurrent.atomics.ExperimentalAtomicApi

@ExperimentalAtomicApi
@Suppress("NOTHING_TO_INLINE")
internal actual inline fun <T> AtomicArray<T>.storeLazyAt(index: Int, value: T) {
    @Suppress("UNCHECKED_CAST", "CAST_NEVER_SUCCEEDS")
    // can't use asJavaAtomicArray due to a bug in older lincheck versions
    this as java.util.concurrent.atomic.AtomicReferenceArray<T>
    lazySet(index, value)
}
