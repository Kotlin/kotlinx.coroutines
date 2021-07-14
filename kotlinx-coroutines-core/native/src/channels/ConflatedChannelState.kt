/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.atomicfu.locks.*

internal actual class ConflatedChannelState : SynchronizedObject() {
    private val _value = atomic<Any?>(EMPTY)

    actual var value: Any?
        get() = _value.value
        set(value) { _value.value = value }

    actual inline fun <T> withLock(block: () -> T): T =
        synchronized(this) {
            block()
        }
}