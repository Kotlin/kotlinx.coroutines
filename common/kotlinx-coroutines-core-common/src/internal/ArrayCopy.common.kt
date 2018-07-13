/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

/**
 * Cross-platform array copy. Overlaps of source and destination are not supported
 */
internal expect fun <E> arraycopy(source: Array<E>, srcPos: Int, destination: Array<E?>, destinationStart: Int, length: Int)