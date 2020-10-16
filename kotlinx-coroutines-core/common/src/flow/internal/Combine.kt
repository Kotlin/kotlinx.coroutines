/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("UNCHECKED_CAST", "NON_APPLICABLE_CALL_FOR_BUILDER_INFERENCE") // KT-32203

package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import kotlin.jvm.*
import kotlin.math.*

private class Update(@JvmField val index: Int, @JvmField val value: Any?)

@PublishedApi
internal suspend fun <R, T> FlowCollector<R>.combineInternal(
    flows: Array<out Flow<T>>,
    arrayFactory: () -> Array<T?>,
    transform: suspend FlowCollector<R>.(Array<T>) -> Unit
): Unit = flowScope { // flow scope so any cancellation within the source flow will cancel the whole scope
    val size = flows.size
    if (size == 0) return@flowScope // bail-out for empty input
    val latestValues = Array<Any?>(size) { UNINITIALIZED }
    val isClosed = Array(size) { false }
    val resultChannel = Channel<Update>(flows.size)
    val nonClosed = LocalAtomicInt(size)
    var remainingAbsentValues = size
    for (i in 0 until size) {
        // Coroutine per flow that keeps track of its value and sends result to downstream
        launch {
            try {
                flows[i].collect { value ->
                    resultChannel.send(Update(i, value))
                    yield() // Emulate fairness for backward compatibility
                }
            } finally {
                isClosed[i] = true
                // Close the channel when there is no more flows
                if (nonClosed.decrementAndGet() == 0) {
                    resultChannel.close()
                }
            }
        }
    }

//    val lastReceivedEpoch = IntArray(size)
//    var currentEpoch = 0
//    while (!resultChannel.isClosedForReceive) {
//        ++currentEpoch
//        var shouldSuspend = true
//        // Start batch
//        var elementsReceived = 0
//        while (true) {
//            // The very first receive in epoch should be suspending
//            val element = if (shouldSuspend) {
//                shouldSuspend = false
//                resultChannel.receiveOrNull()
//            } else {
//                resultChannel.poll()
//            }
//            if (element === null) break // End batch processing, nothing to receive
//            ++elementsReceived
//            val index = element.index
//            // Update valued
//            val previous = latestValues[index]
//            latestValues[index] = element.value
//            if (previous === UNINITIALIZED) --remainingAbsentValues
//            // Check epoch
//            // Received the second value from the same flow in the same epoch -- bail out
//            if (lastReceivedEpoch[index] == currentEpoch) break
//            lastReceivedEpoch[index] = currentEpoch
//        }
//
//        // Process batch result
//        if (remainingAbsentValues == 0 && elementsReceived != 0) {
//            val results = arrayFactory()
//            for (i in 0 until size) {
//                results[i] = latestValues[i] as T?
//            }
//            transform(results as Array<T>)
//        }
//    }

    resultChannel.consumeEach {
        val index = it.index
        val previous = latestValues[index]
        latestValues[index] = it.value
        if (previous === UNINITIALIZED) --remainingAbsentValues
        if (remainingAbsentValues == 0) {
            val results = arrayFactory()
            for (i in 0 until size) {
                results[i] = latestValues[i] as T?
            }
            transform(results as Array<T>)
        }
    }
}

internal fun <T1, T2, R> zipImpl(flow: Flow<T1>, flow2: Flow<T2>, transform: suspend (T1, T2) -> R): Flow<R> =
    unsafeFlow {
        coroutineScope {
            val second = asChannel(flow2)
            /*
             * This approach only works with rendezvous channel and is required to enforce correctness
             * in the following scenario:
             * ```
             * val f1 = flow { emit(1); delay(Long.MAX_VALUE) }
             * val f2 = flowOf(1)
             * f1.zip(f2) { ... }
             * ```
             *
             * Invariant: this clause is invoked only when all elements from the channel were processed (=> rendezvous restriction).
             */
            val collectJob = Job()
            val scopeJob = currentCoroutineContext()[Job]!! // TODO replace with extension when #2245 is here
            (second as SendChannel<*>).invokeOnClose {
                // Optimization to avoid AFE allocation when the other flow is done
                if (collectJob.isActive) collectJob.cancel(AbortFlowException(this@unsafeFlow))
            }

            val newContext = coroutineContext + scopeJob
            val cnt = threadContextElements(newContext)
            try {
                /*
                 * Non-trivial undispatched (because we are in the right context and there is no structured concurrency)
                 * hierarchy:
                 * -Outer coroutineScope that owns the whole zip process
                 * - First flow is collected by the child of coroutineScope, collectJob.
                 *    So it can be safely cancelled as soon as the second flow is done
                 * - **But** the downstream MUST NOT be cancelled when the second flow is done,
                 *    so we emit to downstream from coroutineScope job.
                 * Typically, such hierarchy requires coroutine for collector that communicates
                 * with coroutines scope via a channel, but it's way too expensive, so
                 * we are using this trick instead.
                 */
                withContextUndispatched( coroutineContext + collectJob) {
                    flow.collect { value ->
                        withContextUndispatched(newContext, cnt) {
                            val otherValue = second.receiveOrNull() ?: throw AbortFlowException(this@unsafeFlow)
                            emit(transform(NULL.unbox(value), NULL.unbox(otherValue)))
                        }
                    }
                }
            } catch (e: AbortFlowException) {
                e.checkOwnership(owner = this@unsafeFlow)
            } finally {
                if (!second.isClosedForReceive) second.cancel(AbortFlowException(this@unsafeFlow))
            }
        }
    }

private suspend fun withContextUndispatched(
    newContext: CoroutineContext,
    countOrElement: Any = threadContextElements(newContext),
    block: suspend () -> Unit
): Unit =
    suspendCoroutineUninterceptedOrReturn { uCont ->
        withCoroutineContext(newContext, countOrElement) {
            block.startCoroutineUninterceptedOrReturn(Continuation(newContext) {
                uCont.resumeWith(it)
            })
        }
    }

// Channel has any type due to onReceiveOrNull. This will be fixed after receiveOrClosed
private fun CoroutineScope.asChannel(flow: Flow<*>): ReceiveChannel<Any> = produce {
    flow.collect { value ->
        return@collect channel.send(value ?: NULL)
    }
}
