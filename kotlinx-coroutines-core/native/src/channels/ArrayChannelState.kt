/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlin.math.*

internal actual class ArrayChannelState actual constructor(initialBufferSize: Int) : ArrayBufferState(initialBufferSize) {
    private val _head = atomic(0)
    private val _size = atomic(0)

    actual var head: Int
        get() = _head.value
        set(value) { _head.value = value }

    actual var size: Int
        get() = _size.value
        set(value) { _size.value = value }

    actual fun ensureCapacity(currentSize: Int, capacity: Int) {
        if (currentSize < bufferSize) return
        val newSize = min(bufferSize * 2, capacity)
        val newBuffer = atomicArrayOfNulls<Any?>(newSize)
        for (i in 0 until currentSize) {
            newBuffer[i].value = _buffer.value[(head + i) % bufferSize].value
        }
        _buffer.value = newBuffer
        _bufferSize.value = newSize
        head = 0
    }
}
