/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

internal expect class ArrayChannelState(initialBufferSize: Int) : ArrayBufferState {
    var head: Int
    var size: Int // Invariant: size <= capacity

    fun ensureCapacity(currentSize: Int, capacity: Int)
}
