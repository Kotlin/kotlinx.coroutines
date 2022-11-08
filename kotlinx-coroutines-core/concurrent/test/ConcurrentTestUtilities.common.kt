/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*

internal expect open class SuppressSupportingThrowable() : Throwable
expect val Throwable.suppressed: Array<Throwable>
// Unused on purpose, used manually during debugging sessions
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
