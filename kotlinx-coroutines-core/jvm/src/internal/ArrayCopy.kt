/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

internal actual fun <E> arraycopy(
    source: Array<E>,
    srcPos: Int,
    destination: Array<E?>,
    destinationStart: Int,
    length: Int
) {
    System.arraycopy(source, srcPos, destination, destinationStart, length)
}