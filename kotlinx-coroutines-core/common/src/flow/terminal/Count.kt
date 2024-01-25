@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlin.jvm.*

/**
 * Returns the number of elements in this flow.
 */
public suspend fun <T> Flow<T>.count(): Int  {
    var i = 0
    collect {
        ++i
    }

    return i
}

/**
 * Returns the number of elements matching the given predicate.
 */
public suspend fun <T> Flow<T>.count(predicate: suspend (T) -> Boolean): Int {
    var i = 0
    collect { value ->
        if (predicate(value)) {
            ++i
        }
    }

    return i
}
