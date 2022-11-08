/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

internal actual class CommonThreadLocal<T> {
    private var value: T? = null
    @Suppress("UNCHECKED_CAST")
    actual fun get(): T = value as T
    actual fun set(value: T) { this.value = value }
}

internal actual fun<T> commonThreadLocal(name: Symbol): CommonThreadLocal<T> = CommonThreadLocal()
