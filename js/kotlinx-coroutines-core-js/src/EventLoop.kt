/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*

internal actual fun createEventLoop(): EventLoop = UnconfinedEventLoop()

internal class UnconfinedEventLoop : EventLoop() {
    override fun dispatch(context: CoroutineContext, block: Runnable) {
        throw UnsupportedOperationException("runBlocking event loop is not supported")
    }
}
