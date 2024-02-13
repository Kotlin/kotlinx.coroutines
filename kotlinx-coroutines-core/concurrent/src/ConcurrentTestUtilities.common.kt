/*
 * Copyright 2016-2024 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("unused", "NO_EXPLICIT_VISIBILITY_IN_API_MODE", "NO_EXPLICIT_RETURN_TYPE_IN_API_MODE")

package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*

internal expect open class SuppressSupportingThrowable() : Throwable
expect val Throwable.suppressed: Array<Throwable>
// Unused on purpose, used manually during debugging sessions
@Suppress("unused", "EXTENSION_SHADOWED_BY_MEMBER")
expect fun Throwable.printStackTrace()

expect fun randomWait()

expect fun currentThreadName(): String

inline fun CloseableCoroutineDispatcher.use(block: (CloseableCoroutineDispatcher) -> Unit) {
    try {
        block(this)
    } finally {
        close()
    }
}
