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

private typealias Update = IndexedValue<Any?>

@PublishedApi
internal suspend fun <R, T> FlowCollector<R>.combineInternal(
    flows: Array<out Flow<T>>,
    arrayFactory: () -> Array<T?>, // Array factory is required to workaround array typing on JVM
    transform: suspend FlowCollector<R>.(Array<T>) -> Unit
): Unit = flowScope { // flow scope so any cancellation within the source flow will cancel the whole scope
    val size = flows.size
    if (size == 0) return@flowScope // bail-out for empty input
    val latestValues = arrayOfNulls<Any?>(size)
    latestValues.fill(UNINITIALIZED) // Smaller bytecode & faster that Array(size) { UNINITIALIZED }
    val isClosed = BooleanArray(size)
    val resultChannel = Channel<Update>(flows.size)
    val nonClosed = LocalAtomicInt(size)
    var remainingAbsentValues = size
    for (i in 0 until size) {
        // Coroutine per flow that keeps track of its value and sends result to downstream
        launch {
            try {
                flows[i].collect { value ->
                    resultChannel.send(Update(i, value))
                    yield() // Emulate fairness, giving each flow chance to emit
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

    /*
     * Batch-receive optimization: read updates in batches, but bail-out
     * as soon as we encountered two values from the same source
     */
    val lastReceivedEpoch = ByteArray(size)
    var currentEpoch: Byte = 0
    while (true) {
        ++currentEpoch
        // Start batch
        // The very first receive in epoch should be suspending
        var element = resultChannel.receiveOrNull() ?: break // Channel is closed, nothing to do here
        while (true) {
            val index = element.index
            // Update values
            val previous = latestValues[index]
            latestValues[index] = element.value
            if (previous === UNINITIALIZED) --remainingAbsentValues
            // Check epoch
            // Received the second value from the same flow in the same epoch -- bail out
            if (lastReceivedEpoch[index] == currentEpoch) break
            lastReceivedEpoch[index] = currentEpoch
            element = resultChannel.poll() ?: break
        }

        // Process batch result if there is enough data
        if (remainingAbsentValues == 0) {
            val results = arrayFactory()
            (latestValues as Array<T?>).copyInto(results)
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
