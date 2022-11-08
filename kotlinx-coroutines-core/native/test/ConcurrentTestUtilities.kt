/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

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
    // use the BlackHole value somehow, so even if the compiler gets smarter, it won't remove the object
    val sinkValue = if (BlackHole.sink > 16) 1 else 0
    if (n + sinkValue > 900) sched_yield()
}

@ThreadLocal
private object BlackHole {
    var sink = 1
}

internal actual typealias SuppressSupportingThrowable = SuppressSupportingThrowableImpl

actual val Throwable.suppressed: Array<Throwable>
    get() = (this as? SuppressSupportingThrowableImpl)?.suppressed ?: emptyArray()

@Suppress("EXTENSION_SHADOWED_BY_MEMBER", "unused")
actual fun Throwable.printStackTrace() = printStackTrace()

actual fun currentThreadName(): String = Worker.current.name
