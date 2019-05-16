/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

@PublishedApi
internal class SafeCollector<T>(
    private val collector: FlowCollector<T>,
    collectContext: CoroutineContext
) : FlowCollector<T>, SynchronizedObject() {

    private val collectContext = collectContext.minusKey(Job).minusId()
    private var lastObservedContext: CoroutineContext? = null

    override suspend fun emit(value: T)  {
        /*
         * Benign data-race here:
         * We read potentially racy published coroutineContext, but we only use it for
         * referential comparison (=> thus safe) and are not using it for actual comparisons.
         */
        val currentContext = coroutineContext
        if (lastObservedContext !== currentContext) {
            val emitContext = currentContext.minusKey(Job).minusId()
            if (emitContext != collectContext) {
                error(
                    "Flow invariant is violated: flow was collected in $collectContext, but emission happened in $emitContext. " +
                            "Please refer to 'flow' documentation or use 'flowOn' instead"
                )
            }
            // Racy publication
            lastObservedContext = currentContext
        }
        collector.emit(value) // TCE
    }
}
