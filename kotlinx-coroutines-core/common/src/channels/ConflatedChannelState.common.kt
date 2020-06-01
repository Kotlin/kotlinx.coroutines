/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

internal expect class ConflatedChannelState() {
    var value: Any?
    inline fun <T> withLock(block: () -> T): T
}