/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

/**
 * This exception is thrown when operator need no more elements from the flow.
 * This exception should never escape outside of operator's implementation.
 * This exception can be safely ignored by non-terminal flow operator if and only if it was caught by its owner
 * (see usages of [checkOwnership]).
 */
internal expect class AbortFlowException(owner: FlowCollector<*>) : CancellationException {
    public val owner: FlowCollector<*>
}

internal fun AbortFlowException.checkOwnership(owner: FlowCollector<*>) {
    if (this.owner !== owner) throw this
}

/**
 * Exception used to cancel child of [scopedFlow] without cancelling the whole scope.
 */
internal expect class ChildCancelledException() : CancellationException

@Suppress("NOTHING_TO_INLINE")
@PublishedApi
internal inline fun checkIndexOverflow(index: Int): Int {
    if (index < 0) {
        throw ArithmeticException("Index overflow has happened")
    }
    return index
}
