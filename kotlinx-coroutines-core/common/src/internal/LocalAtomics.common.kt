/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

/*
 * These are atomics that are used as local variables
 * where atomicfu doesn't support its tranformations.
 *
 * Have `Local` prefix to avoid AFU clashes during star-imports
 */
internal expect class LocalAtomicInt(value: Int) {
    fun get(): Int
    fun set(value: Int)
    fun decrementAndGet(): Int
}

internal inline var LocalAtomicInt.value
    get() = get()
    set(value) = set(value)
