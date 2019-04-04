/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.flow.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

@PublishedApi
internal class SafeCollector<T>(
    private val collector: FlowCollector<T>,
    private val interceptor: ContinuationInterceptor?
) : FlowCollector<T>, SynchronizedObject() {

    override suspend fun emit(value: T)  {
        if (interceptor != coroutineContext[ContinuationInterceptor]) {
            error(
                "Flow invariant is violated: flow was collected in $interceptor, but emission happened in ${coroutineContext[ContinuationInterceptor]}. " +
                        "Please refer to 'flow' documentation or use 'flowOn' instead"
            )
        }
        collector.emit(value)
    }
}
