/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

// internal debugging tools for string representation

internal actual val Any.hexAddress: String
    get() = Integer.toHexString(System.identityHashCode(this))

internal actual fun Continuation<*>.toDebugString(): String = when (this) {
    is DispatchedContinuation -> toString()
    // Workaround for #858
    else -> runCatching { "$this@$hexAddress" }.getOrElse { "${this::class.java.name}@$hexAddress" }
}

internal actual val Any.classSimpleName: String get() = this::class.java.simpleName
