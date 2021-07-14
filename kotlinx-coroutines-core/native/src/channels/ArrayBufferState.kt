/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.atomicfu.locks.*

internal actual open class ArrayBufferState actual constructor(initialBufferSize: Int) : SynchronizedObject() {
    protected val _buffer = atomic(atomicArrayOfNulls<Any?>(initialBufferSize))
    protected val _bufferSize = atomic(initialBufferSize)

    actual val bufferSize: Int
        get() = _bufferSize.value

    actual fun getBufferAt(index: Int): Any? =
        _buffer.value[index].value

    actual fun setBufferAt(index: Int, value: Any?) {
        _buffer.value[index].value = value
    }

    actual inline fun <T> withLock(block: () -> T): T =
        synchronized(this) {
            block()
        }
}
