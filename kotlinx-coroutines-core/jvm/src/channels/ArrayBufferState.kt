/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

internal actual open class ArrayBufferState actual constructor(initialBufferSize: Int) {
    protected var buffer: Array<Any?> = arrayOfNulls<Any?>(initialBufferSize)

    actual val bufferSize: Int get() = buffer.size

    actual fun getBufferAt(index: Int): Any? =
        buffer[index]

    actual fun setBufferAt(index: Int, value: Any?) {
        buffer[index] = value
    }

    actual inline fun <T> withLock(block: () -> T): T =
        synchronized(this) {
            block()
        }
}
