/*
 * Copyright 2016-2024 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlin.coroutines.*

@InternalCoroutinesApi
public fun runTestCoroutine(context: CoroutineContext, block: suspend CoroutineScope.() -> Unit) {
    val newContext = GlobalScope.newCoroutineContext(context)
    val coroutine = object: AbstractCoroutine<Unit>(newContext, true, true) {}
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
    runEventLoop()
    if (coroutine.isCancelled) throw coroutine.getCancellationException().let { it.cause ?: it }
}