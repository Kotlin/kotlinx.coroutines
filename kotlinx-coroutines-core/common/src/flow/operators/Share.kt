/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.internal.*
import kotlin.coroutines.*
import kotlin.jvm.*

// -------------------------------- shareIn --------------------------------

/**
 * Converts a _cold_ [Flow] into a _hot_ [SharedFlow] that is started in the given coroutine [scope],
 * sharing emissions from a single running instance of upstream flow with multiple downstream subscribers,
 * and replaying a specified number of [replay] values to new subscribers. See [SharedFlow] documentation
 * on a general concepts of shared flows.
 *
 * This function throws [IllegalArgumentException] on unsupported values of parameters of combinations thereof.
 *
 * ### Operator fusion
 *
 * TODO: Fusion with preceding [buffer] operators.
 *
 * Application of [flowOn][Flow.flowOn], [buffer] with [RENDEZVOUS][Channel.RENDEZVOUS] capacity,
 * or [cancellable] operators to a shared flow has no effect.
 *
 * @param scope the coroutine scope in which sharing is started.
 * @param replay the number of values replayed to new subscribers (cannot be negative).
 * @param started the strategy that controls when sharing is started and stopped
 *   (optional, default to [eagerly][SharingStarted.Eagerly] starting the sharing without waiting for subscribers).
 * @param initialValue the initial value in the replay cache (optional, defaults to nothing, supported only when `replay > 0`).
 *   This value is also used when shared flow buffer is reset using [SharingStarted.WhileSubscribed] strategy
 *   with `replayExpirationMillis` parameter.
 */
@ExperimentalCoroutinesApi
public fun <T> Flow<T>.shareIn(
    scope: CoroutineScope,
    replay: Int,
    started: SharingStarted = SharingStarted.Eagerly,
    initialValue: T = NO_VALUE as T
): SharedFlow<T> {
    val shared = MutableSharedFlow<T>(
        replay = replay,
        extraBufferCapacity = Channel.CHANNEL_DEFAULT_CAPACITY,
        initialValue = initialValue
    )
    scope.launchSharing(this, shared, started)
    return shared.asSharedFlow()
}

internal fun <T> CoroutineScope.launchSharing(upstream: Flow<T>, shared: MutableSharedFlow<T>, started: SharingStarted) {
    launch { // the single coroutine to rule the sharing
        try {
            started.commandFlow(shared.subscriptionCount)
                .distinctUntilChanged()
                .collectLatest { // cancels block on new emission
                    when (it) {
                        SharingCommand.START -> upstream.collect(shared) // can be cancelled
                        SharingCommand.STOP -> { /* just cancel and do nothing else */ }
                        SharingCommand.STOP_AND_RESET_BUFFER -> shared.resetBuffer()
                    }
                }
        } finally {
            shared.resetBuffer() // on any completion/cancellation/failure of sharing
        }
    }
}

// -------------------------------- stateIn --------------------------------

/**
 * Converts a _cold_ [Flow] into a _hot_ [StateFlow] that is started in the given coroutine [scope],
 * sharing the most recently emitted value by single running instance of upstream flow with multiple
 * downstream subscribers. See [StateFlow] documentation on a general concepts of state flows.
 *
 * ### Operator fusion
 *
 * TODO: Fusion with preceding [buffer] operators.
 *
 * Application of [flowOn][Flow.flowOn], [conflate][Flow.conflate],
 * [buffer] with [CONFLATED][Channel.CONFLATED] or [RENDEZVOUS][Channel.RENDEZVOUS] capacity,
 * [distinctUntilChanged][Flow.distinctUntilChanged], or [cancellable] operators to a state flow has no effect.
 *
 * @param scope the coroutine scope in which sharing is started.
 * @param started the strategy that controls when sharing is started and stopped
 *   (optional, default to [eagerly][SharingStarted.Eagerly] starting the sharing without waiting for subscribers).
 * @param initialValue the initial value of the state flow.
 *   This value is also used when state flow is reset using [SharingStarted.WhileSubscribed] strategy
 *   with `replayExpirationMillis` parameter.
 */
@ExperimentalCoroutinesApi
public fun <T> Flow<T>.stateIn(
    scope: CoroutineScope,
    started: SharingStarted = SharingStarted.Eagerly,
    initialValue: T
): StateFlow<T> {
    val state = MutableStateFlow(initialValue)
    scope.launchSharing(this, state, started)
    return state.asStateFlow()
}

/**
 * Starts the upstream flow in a given [scope], suspends until the first value is emitted, and returns a _hot_
 * [StateFlow] of future emissions, sharing the most recently emitted value by this running instance of upstream flow
 * with multiple downstream subscribers. See [StateFlow] documentation on a general concepts of state flows.
 *
 * @param scope the coroutine scope in which sharing is started.
 */
@ExperimentalCoroutinesApi
public suspend fun <T> Flow<T>.stateIn(scope: CoroutineScope): StateFlow<T> {
    val result = CompletableDeferred<StateFlow<T>>()
    scope.launchSharingDeferred(this, result)
    return result.await()
}

private fun <T> CoroutineScope.launchSharingDeferred(upstream: Flow<T>, result: CompletableDeferred<StateFlow<T>>) {
    launch {
        var state: MutableStateFlow<T>? = null
        upstream.collect { value ->
            state?.let { it.value = value } ?: run {
                state = MutableStateFlow(value).also {
                    result.complete(it.asStateFlow())
                }
            }
        }
    }
}

// -------------------------------- asSharedFlow/asStateFlow --------------------------------

/**
 * Represents this mutable shared flow as read-only shared flow.
 */
@ExperimentalCoroutinesApi
public fun <T> MutableSharedFlow<T>.asSharedFlow(): SharedFlow<T> =
    object : SharedFlow<T> by this {}

/**
 * Represents this mutable state flow as read-only state flow.
 */
@ExperimentalCoroutinesApi
public fun <T> MutableStateFlow<T>.asStateFlow(): StateFlow<T> =
    object : StateFlow<T> by this {}

// -------------------------------- onSubscription --------------------------------

/**
 * Returns a flow that invokes the given [action] **after** this shared flow starts to be collected
 * (after subscription is registered). The [action] is called before any value is emitted from the upstream
 * flow to this subscription yet, but it is guaranteed that all future emissions to the upstream flow will be
 * collected by this subscription.
 *
 * The receiver of the [action] is [FlowCollector], so `onSubscription` can emit additional elements.
 */
@ExperimentalCoroutinesApi
public fun <T> SharedFlow<T>.onSubscription(action: suspend FlowCollector<T>.() -> Unit): SharedFlow<T> =
    SubscribedSharedFlow(this, action)

private class SubscribedSharedFlow<T>(
    private val sharedFlow: SharedFlow<T>,
    private val action: suspend FlowCollector<T>.() -> Unit
) : SharedFlow<T> by sharedFlow {
    override suspend fun collect(collector: FlowCollector<T>) =
        sharedFlow.collect(SubscribedFlowCollector(collector, action))
}

internal class SubscribedFlowCollector<T>(
    private val collector: FlowCollector<T>,
    private val action: suspend FlowCollector<T>.() -> Unit
) : FlowCollector<T> by collector {
    suspend fun onSubscription() {
        val safeCollector = SafeCollector(collector, coroutineContext)
        try {
            safeCollector.action()
        } finally {
            safeCollector.releaseIntercepted()
        }
        if (collector is SubscribedFlowCollector) collector.onSubscription()
    }
}

