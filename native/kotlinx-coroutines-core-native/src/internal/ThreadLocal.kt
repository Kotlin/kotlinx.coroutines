/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal
import kotlin.native.concurrent.*

@Suppress("ACTUAL_WITHOUT_EXPECT")
internal actual typealias NativeThreadLocal = kotlin.native.ThreadLocal

internal actual class CommonThreadLocal<T> actual constructor(supplier: () -> T) {
    private val value = supplier()
    actual fun get(): T = value
}
