/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.flow.*

/**
 * An internal interface that marks the flow impls with distinct values, so that
 * application of [distinctUntilChanged] can be optimized away. A class implementing
 * this interface can be conditionally distinct via [isDefaultEquivalence] without
 * having to have multiple copies of the same code.
 */
internal interface DistinctFlow<T> : Flow<T> {
    val isDefaultEquivalence: Boolean // true when using default equivalence
}

/**
 * An analogue of the [flow] builder that does not check the context of execution of the resulting flow,
 * and the implementation must also guarantee that all emitted values are distinct, so that [distinctUntilChanged]
 * can be optimized away. Used in our own operators where we trust these contracts to be met.
 */
@PublishedApi
internal inline fun <T> unsafeDistinctFlow(
    isDefaultEquivalence: Boolean = true,
    @BuilderInference crossinline block: suspend FlowCollector<T>.() -> Unit
): Flow<T> =
    object : DistinctFlow<T> {
        override val isDefaultEquivalence = isDefaultEquivalence
        override suspend fun collect(collector: FlowCollector<T>) = collector.block()
    }
