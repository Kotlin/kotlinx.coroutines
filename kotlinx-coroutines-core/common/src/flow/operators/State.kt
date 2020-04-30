/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.jvm.*

/**
 * A job that is created by [stateIn] operator.
 *
 * **Preview feature**: The design of `stateIn` operator is tentative and could change.
 */
@FlowPreview
public interface StateFlowJob<out T> : StateFlow<T>, Job

/**
 * Launches a coroutine that collects this [Flow] and emits all the collected values as the resulting [StateFlow].
 * The result of this function is both a [StateFlow] and a [Job]. This call effectively turns a cold [Flow] into a
 * hot, active [Flow], making the most recently emitted value available for consumption at any time via
 * [StateFlow.value]. This function returns immediately. The state flow it creates is initially set
 * to the specified default [value]. As an alternative a version of `stateIn` without a default value can be used,
 * which suspend until the source flow emits a first value.
 *
 * The resulting coroutine can be cancelled by [cancelling][CoroutineScope.cancel] the [scope] in which it is
 * launched or by [cancelling][Job.cancel] the resulting [Job].
 *
 * Errors in the source flow are not propagated to the [scope] but [close][MutableStateFlow.close] the resulting
 * [StateFlow] or are rethrown to the caller of `stateIn` if they happen before emission of the first value.
 *
 * **Preview feature**: The design of `stateIn` operator is tentative and could change.
 */
@FlowPreview
public fun <T> Flow<T>.stateIn(scope: CoroutineScope, value: T): StateFlowJob<T> {
    val state = StateFlow(value)
    val job = scope.launchStateJob(this, null, state)
    return StateFlowJobImpl(state, job)
}

/**
 * Launches a coroutine that collects this [Flow] and emits all the collected values as the resulting [StateFlow].
 * The result of this function is both a [StateFlow] and a [Job]. This call effectively turns a cold [Flow] into a
 * hot, active [Flow], making the most recently emitted value available for consumption at any time via
 * [StateFlow.value]. This call suspends until the source flow the emits first value and
 * throws [NoSuchElementException] if the flow was empty. As an alternative, a version of `stateIn` with a default
 * value can be used, which does not suspend.
 *
 * The resulting coroutine can be cancelled by [cancelling][CoroutineScope.cancel] the [scope] in which it is
 * launched or by [cancelling][Job.cancel] the resulting [Job].
 *
 * Errors in the source flow are not propagated to the [scope] but [close][MutableStateFlow.close] the resulting
 * [StateFlow] or are rethrown to the caller of `stateIn` if they happen before emission of the first value.
 *
 * **Preview feature**: The design of `stateIn` operator is tentative and could change.
 */
@FlowPreview
public suspend fun <T> Flow<T>.stateIn(scope: CoroutineScope): StateFlowJob<T> {
    val deferredResult = CompletableDeferred<StateFlowJob<T>>()
    scope.launchStateJob(this, deferredResult, null)
    return deferredResult.await() // tail call
}

private fun <T> CoroutineScope.launchStateJob(
    flow: Flow<T>,
    deferredResult: CompletableDeferred<StateFlowJob<T>>?,
    initialState: MutableStateFlow<T>?
) = launch {
    var state: MutableStateFlow<T>? = initialState
    var exception: Throwable? = null
    try {
        flow.collect { value ->
            // Update state flow if initialized
            state?.let { it.value = value } ?: run {
                // Or create state on the first value if state was not created yet (first value)
                state = StateFlow(value).also {
                    // resume stateIn call with initialized StateFlow and current job
                    deferredResult?.complete(StateFlowJobImpl(it, coroutineContext[Job]!!))
                }
            }
        }
    } catch (e: Throwable) {
        // Ignore cancellation exception -- it is a normal way to stop the flow
        if (e !is CancellationException) exception = e
    }
    // Close the state flow with exception if initialized
    state?.apply { close(exception) } ?: run {
        // Or complete the deferred exceptionally if the state was not create yet)
        deferredResult?.completeExceptionally(exception ?: NoSuchElementException("Expected at least one element"))
    }
}

private class StateFlowJobImpl<T>(state: StateFlow<T>, job: Job) : StateFlowJob<T>, StateFlow<T> by state, Job by job