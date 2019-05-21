/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.internal.ScopeCoroutine
import kotlin.coroutines.*

@PublishedApi
internal class SafeCollector<T>(
    private val collector: FlowCollector<T>,
    collectContext: CoroutineContext
) : FlowCollector<T> {

    private val collectContext = collectContext.minusKey(Job).minusId()
    private var lastEmissionContext: CoroutineContext? = null

    override suspend fun emit(value: T)  {
        /*
         * Benign data-race here:
         * We read potentially racy published coroutineContext, but we only use it for
         * referential comparison (=> thus safe) and are not using it for structural comparisons.
         */
        val currentContext = coroutineContext
        val observedContext = lastEmissionContext
        if (observedContext !== currentContext) {
            if (observedContext !== null) checkJobs(observedContext, currentContext)
            val emitContext = currentContext.minusKey(Job).minusId()
            if (emitContext != collectContext) {
                    error(
                        "Flow invariant is violated: flow was collected in $collectContext, but emission happened in $emitContext. " +
                                "Please refer to 'flow' documentation or use 'flowOn' instead"
                    )
                }
            lastEmissionContext = currentContext
        }
        collector.emit(value) // TCE
    }

    private fun checkJobs(observedContext: CoroutineContext, currentContext: CoroutineContext) {
        val previousJob = observedContext[Job].transitiveCoroutineParent()
        val currentJob = currentContext[Job].transitiveCoroutineParent()
        check(previousJob === currentJob) { "Flow invariant is violated: emissions from different coroutines are detected ($currentContext and $lastEmissionContext). " +
                "FlowCollector is not thread-safe and concurrent emissions are prohibited. To mitigate this restriction please use 'flowChannel' builder instead of 'flow'" }
    }

    private fun Job?.transitiveCoroutineParent(): Job? {
        if (this === null) return null
        if (this !is ScopeCoroutine<*>) return this
        return parent.transitiveCoroutineParent()
    }
}
