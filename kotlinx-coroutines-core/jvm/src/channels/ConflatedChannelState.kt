/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

internal actual class ConflatedChannelState {
    actual var value: Any? = EMPTY

    actual inline fun <T> withLock(block: () -> T): T =
        synchronized(this) {
            block()
        }
}