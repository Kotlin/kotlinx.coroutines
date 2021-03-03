/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.coroutines.*

internal actual class SafeCollector<T> actual constructor(
    internal actual val collector: FlowCollector<T>,
    internal actual val collectContext: CoroutineContext
) : FlowCollector<T> {

    // Note, it is non-capturing lambda, so no extra allocation during init of SafeCollector
    internal actual val collectContextSize = collectContext.fold(0) { count, _ -> count + 1 }
    private var lastEmissionContext: CoroutineContext? = null

    override suspend fun emit(value: T) {
        val currentContext = currentCoroutineContext()
        currentContext.ensureActive()
        if (lastEmissionContext !== currentContext) {
            checkContext(currentContext)
            lastEmissionContext = currentContext
        }
        collector.emit(value)
    }

    public actual fun releaseIntercepted() {
    }
}
