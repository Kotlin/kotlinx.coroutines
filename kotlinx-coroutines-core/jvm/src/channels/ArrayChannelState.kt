/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlin.math.*

internal actual class ArrayChannelState actual constructor(initialBufferSize: Int) : ArrayBufferState(initialBufferSize) {
    actual var head = 0
    actual var size = 0

    actual fun ensureCapacity(currentSize: Int, capacity: Int) {
        if (currentSize < buffer.size) return
        val newSize = min(buffer.size * 2, capacity)
        val newBuffer = arrayOfNulls<Any?>(newSize)
        for (i in 0 until currentSize) {
            newBuffer[i] = buffer[(head + i) % buffer.size]
        }
        buffer = newBuffer
        head = 0
    }
}
