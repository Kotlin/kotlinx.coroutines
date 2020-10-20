/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.atomicfu.*

internal actual class LocalAtomicInt actual constructor(value: Int) {

    private val iRef = atomic(value)

    actual fun set(value: Int) {
        iRef.value = value
    }

    actual fun get(): Int = iRef.value

    actual fun decrementAndGet(): Int = iRef.decrementAndGet()
}
