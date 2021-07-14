/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

internal expect open class ArrayBufferState(initialBufferSize: Int) {
    val bufferSize: Int

    fun getBufferAt(index: Int): Any?
    fun setBufferAt(index: Int, value: Any?)

    inline fun <T> withLock(block: () -> T): T
}
