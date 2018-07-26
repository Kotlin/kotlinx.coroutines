/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.io

interface WriterSession {
    fun request(min: Int): ByteBuffer?
    fun written(n: Int)
}

interface WriterSuspendSession : WriterSession {
    suspend fun tryAwait(n: Int)
}
