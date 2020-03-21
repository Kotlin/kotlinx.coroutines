/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.math.*

internal actual val DEBUG: Boolean = false

internal actual val Any.hexAddress: String get() = abs(id().let { if (it == Int.MIN_VALUE) 0 else it }).toString(16)

internal actual val Any.classSimpleName: String get() = this::class.simpleName ?: "Unknown"

@SymbolName("Kotlin_Any_hashCode")
external fun Any.id(): Int // Note: can return negative value on K/N

internal actual inline fun assert(value: () -> Boolean) {}
