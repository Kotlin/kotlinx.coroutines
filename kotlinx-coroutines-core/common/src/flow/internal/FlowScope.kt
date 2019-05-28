/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.intrinsics.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

/**
 * Creates a flow that also provides a [CoroutineScope] for each collector.
 *
 * Provided [CoroutineScope] is similar to [coroutineScope] with the only exception that it *ties* lifecycle of children
 * and itself regarding the cancellation, thus being cancelled when one of the children becomes cancelled.
 * For example:
 * ```
 * scopedFlow {
 *     launch {
 *         throw CancellationException()
 *     }
 * } // <- CE will be rethrown here
 * ```
 *
 * Basically, it is shorthand for:
 * ```
 * flow {
 *     coroutineScope {
 *         ...
 *     }
 * }
 * ```
 * with additional constraint on cancellation.
 * To cancel child without cancelling itself, `cancel(ChildCancelledException())` should be used.
 */
internal fun <R> scopedFlow(@BuilderInference block: suspend FlowScope<Unit, R>.() -> Unit): Flow<R> =
    object : Flow<R> {
        override suspend fun collect(collector: FlowCollector<R>) {
            suspendCoroutineUninterceptedOrReturn<Unit> { uCont ->
                val coroutine = FlowScope(collector, uCont.context, uCont)
                coroutine.startUndispatchedOrReturn(coroutine, block)
            }
        }
    }

internal class FlowScope<T, R>(
    private val collector: FlowCollector<R>,
    context: CoroutineContext,
    uCont: Continuation<T>
) : ScopeCoroutine<T>(context, uCont), FlowCollector<R> {

    public override fun cancelOnChildCancellation(cause: CancellationException) = cause !is ChildCancelledException

    override suspend fun emit(value: R) = collector.emit(value)
}

internal class ChildCancelledException : CancellationException(null)
