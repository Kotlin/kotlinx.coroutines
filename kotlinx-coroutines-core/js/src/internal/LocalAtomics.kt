/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

internal actual class LocalAtomicInt actual constructor(private var value: Int) {
    actual fun set(value: Int) {
        this.value = value
    }

    actual fun get(): Int = value

    actual fun decrementAndGet(): Int = --value
}
