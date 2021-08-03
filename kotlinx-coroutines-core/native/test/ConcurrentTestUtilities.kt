/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

import kotlinx.atomicfu.*
import kotlinx.coroutines.internal.*
import platform.posix.*
import kotlin.native.concurrent.*
import kotlin.random.*

actual fun randomWait() {
    val n = Random.nextInt(1000)
    if (n < 500) return // no wait 50% of time
    repeat(n) {
        BlackHole.sink *= 3
    }
    if (n > 900) sched_yield()
}

@ThreadLocal
private object BlackHole {
    var sink = 1
}

internal actual typealias SuppressSupportingThrowable = SuppressSupportingThrowableImpl

actual val Throwable.suppressed: Array<Throwable>
    get() = (this as? SuppressSupportingThrowableImpl)?.suppressed ?: emptyArray()

@Suppress("EXTENSION_SHADOWED_BY_MEMBER")
actual fun Throwable.printStackTrace() = printStackTrace()

