/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

import kotlin.random.*

actual fun randomWait() {
    val n = Random.nextInt(1000)
    if (n < 500) return // no wait 50% of time
    repeat(n) {
        BlackHole.sink *= 3
    }
    if (n > 900) Thread.yield()
}

private object BlackHole {
    @Volatile
    var sink = 1
}

@Suppress("ACTUAL_WITHOUT_EXPECT")
internal actual typealias SuppressSupportingThrowable = Throwable

@Suppress("EXTENSION_SHADOWED_BY_MEMBER")
actual fun Throwable.printStackTrace() = printStackTrace()

actual fun currentThreadName(): String = Thread.currentThread().name
