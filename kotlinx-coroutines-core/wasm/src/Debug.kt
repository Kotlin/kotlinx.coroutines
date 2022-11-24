/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

internal actual val DEBUG: Boolean = false

internal actual val Any.hexAddress: String
    get() = this.hashCode().toString()

internal actual val Any.classSimpleName: String get() = this::class.simpleName ?: "Unknown"

internal actual inline fun assert(value: () -> Boolean) {}
