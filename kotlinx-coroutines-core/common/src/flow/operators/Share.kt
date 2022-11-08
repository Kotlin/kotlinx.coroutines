/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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
 * sharing emissions from a single running instance of the upstream flow with multiple downstream subscribers,
 * and replaying a specified number of [replay] values to new subscribers. See the [SharedFlow] documentation
 * for the general concepts of shared flows.
 *
 * The starting of the sharing coroutine is controlled by the [started] parameter. The following options
 * are supported.
 *
 * * [Eagerly][SharingStarted.Eagerly] &mdash; the upstream flow is started even before the first subscriber appears. Note
 *   that in this case all values emitted by the upstream beyond the most recent values as specified by
 *   [replay] parameter **will be immediately discarded**.
 * * [Lazily][SharingStarted.Lazily] &mdash; starts the upstream flow after the first subscriber appears, which guarantees
 *   that this first subscriber gets all the emitted values, while subsequent subscribers are only guaranteed to
 *   get the most recent [replay] values. The upstream flow continues to be active even when all subscribers
 *   disappear, but only the most recent [replay] values are cached without subscribers.
 * * [WhileSubscribed()][SharingStarted.WhileSubscribed] &mdash; starts the upstream flow when the first subscriber
 *   appears, immediately stops when the last subscriber disappears, keeping the replay cache forever.
 *   It has additional optional configuration parameters as explained in its documentation.
 * * A custom strategy can be supplied by implementing the [SharingStarted] interface.
 *
 * The `shareIn` operator is useful in situations when there is a _cold_ flow that is expensive to create and/or
 * to maintain, but there are multiple subscribers that need to collect its values. For example, consider a
 * flow of messages coming from a backend over the expensive network connection, taking a lot of
 * time to establish. Conceptually, it might be implemented like this:
 *
 * ```
 * val backendMessages: Flow<Message> = flow {
 *     connectToBackend() // takes a lot of time
 *     try {
 *       while (true) {
 *           emit(receiveMessageFromBackend())
 *       }
 *     } finally {
 *         disconnectFromBackend()
 *     }
 * }
 * ```
 *
 * If this flow is directly used in the application, then every time it is collected a fresh connection is
 * established, and it will take a while before messages start flowing. However, we can share a single connection
 * and establish it eagerly like this:
 *
 * ```
 * val messages: SharedFlow<Message> = backendMessages.shareIn(scope, SharingStarted.Eagerly)
 * ```
 *
 * Now a single connection is shared between all collectors from `messages`, and there is a chance that the connection
 * is already established by the time it is needed.
 *
 * ### Upstream completion and error handling
 *
 * **Normal completion of the upstream flow has no effect on subscribers**, and the sharing coroutine continues to run. If a
 * strategy like [SharingStarted.WhileSubscribed] is used, then the upstream can get restarted again. If a special
 * action on upstream completion is needed, then an [onCompletion] operator can be used before the
 * `shareIn` operator to emit a special value in this case, like this:
 *
 * ```
 * backendMessages
 *     .onCompletion { cause -> if (cause == null) emit(UpstreamHasCompletedMessage) }
 *     .shareIn(scope, SharingStarted.Eagerly)
 * ```
 *
 * Any exception in the upstream flow terminates the sharing coroutine without affecting any of the subscribers,
 * and will be handled by the [scope] in which the sharing coroutine is launched. Custom exception handling
 * can be configured by using the [catch] or [retry] operators before the `shareIn` operator.
 * For example, to retry connection on any `IOException` with 1 second delay between attempts, use:
 *
 * ```
 * val messages = backendMessages
 *     .retry { e ->
 *         val shallRetry = e is IOException // other exception are bugs - handle them
 *         if (shallRetry) delay(1000)
 *         shallRetry
 *     }
 *     .shareIn(scope, SharingStarted.Eagerly)
 * ```
 *
 * ### Initial value
 *
 * When a special initial value is needed to signal to subscribers that the upstream is still loading the data,
 * use the [onStart] operator on the upstream flow. For example:
 *
 * ```
 * backendMessages
 *     .onStart { emit(UpstreamIsStartingMessage) }
 *     .shareIn(scope, SharingStarted.Eagerly, 1) // replay one most recent message
 * ```
 *
 * ### Buffering and conflation
 *
 * The `shareIn` operator runs the upstream flow in a separate coroutine, and buffers emissions from upstream as explained
 * in the [buffer] operator's description, using a buffer of [replay] size or the default (whichever is larger).
 * This default buffering can be overridden with an explicit buffer configuration by preceding the `shareIn` call
 * with [buffer] or [conflate], for example:
 *
 * * `buffer(0).shareIn(scope, started, 0)` &mdash; overrides the default buffer size and creates a [SharedFlow] without a buffer.
 *   Effectively, it configures sequential processing between the upstream emitter and subscribers,
 *   as the emitter is suspended until all subscribers process the value. Note, that the value is still immediately
 *   discarded when there are no subscribers.
 * * `buffer(b).shareIn(scope, started, r)` &mdash; creates a [SharedFlow] with `replay = r` and `extraBufferCapacity = b`.
 * * `conflate().shareIn(scope, started, r)` &mdash; creates a [SharedFlow] with `replay = r`, `onBufferOverflow = DROP_OLDEST`,
 *   and `extraBufferCapacity = 1` when `replay == 0` to support this strategy.
 *
 * ### Operator fusion
 *
 * Application of [flowOn][Flow.flowOn], [buffer] with [RENDEZVOUS][Channel.RENDEZVOUS] capacity,
 * or [cancellable] operators to the resulting shared flow has no effect.
 *
 * ### Exceptions
 *
 * This function throws [IllegalArgumentException] on unsupported values of parameters or combinations thereof.
 *
 * @param scope the coroutine scope in which sharing is started.
 * @param started the strategy that controls when sharing is started and stopped.
 * @param replay the number of values replayed to new subscribers (cannot be negative, defaults to zero).
 */
public fun <T> Flow<T>.shareIn(
    scope: CoroutineScope,
    started: SharingStarted,
    replay: Int = 0
): SharedFlow<T> {
    val config = configureSharing(replay)
    val shared = MutableSharedFlow<T>(
        replay = replay,
        extraBufferCapacity = config.extraBufferCapacity,
        onBufferOverflow = config.onBufferOverflow
    )
    @Suppress("UNCHECKED_CAST")
    val job = scope.launchSharing(config.context, config.upstream, shared, started, NO_VALUE as T)
    return ReadonlySharedFlow(shared, job)
}

private class SharingConfig<T>(
    @JvmField val upstream: Flow<T>,
    @JvmField val extraBufferCapacity: Int,
    @JvmField val onBufferOverflow: BufferOverflow,
    @JvmField val context: CoroutineContext
)

// Decomposes upstream flow to fuse with it when possible
private fun <T> Flow<T>.configureSharing(replay: Int): SharingConfig<T> {
    assert { replay >= 0 }
    val defaultExtraCapacity = replay.coerceAtLeast(Channel.CHANNEL_DEFAULT_CAPACITY) - replay
    // Combine with preceding buffer/flowOn and channel-using operators
    if (this is ChannelFlow) {
        // Check if this ChannelFlow can operate without a channel
        val upstream = dropChannelOperators()
        if (upstream != null) { // Yes, it can => eliminate the intermediate channel
            return SharingConfig(
                upstream = upstream,
                extraBufferCapacity = when (capacity) {
                    Channel.OPTIONAL_CHANNEL, Channel.BUFFERED, 0 -> // handle special capacities
                        when {
                            onBufferOverflow == BufferOverflow.SUSPEND -> // buffer was configured with suspension
                                if (capacity == 0) 0 else defaultExtraCapacity // keep explicitly configured 0 or use default
                            replay == 0 -> 1 // no suspension => need at least buffer of one
                            else -> 0 // replay > 0 => no need for extra buffer beyond replay because we don't suspend
                        }
                    else -> capacity // otherwise just use the specified capacity as extra capacity
                },
                onBufferOverflow = onBufferOverflow,
                context = context
            )
        }
    }
    // Add sharing operator on top with a default buffer
    return SharingConfig(
        upstream = this,
        extraBufferCapacity = defaultExtraCapacity,
        onBufferOverflow = BufferOverflow.SUSPEND,
        context = EmptyCoroutineContext
    )
}

// Launches sharing coroutine
private fun <T> CoroutineScope.launchSharing(
    context: CoroutineContext,
    upstream: Flow<T>,
    shared: MutableSharedFlow<T>,
    started: SharingStarted,
    initialValue: T
): Job {
    /*
     * Conditional start: in the case when sharing and subscribing happens in the same dispatcher, we want to
     * have the following invariants preserved:
     * * Delayed sharing strategies have a chance to immediately observe consecutive subscriptions.
     *   E.g. in the cases like `flow.shareIn(...); flow.take(1)` we want sharing strategy to see the initial subscription
     * * Eager sharing does not start immediately, so the subscribers have actual chance to subscribe _prior_ to sharing.
     */
    val start = if (started == SharingStarted.Eagerly) CoroutineStart.DEFAULT else CoroutineStart.UNDISPATCHED
    return launch(context, start = start) { // the single coroutine to rule the sharing
        // Optimize common built-in started strategies
        when {
            started === SharingStarted.Eagerly -> {
                // collect immediately & forever
                upstream.collect(shared)
            }
            started === SharingStarted.Lazily -> {
                // start collecting on the first subscriber - wait for it first
                shared.subscriptionCount.first { it > 0 }
                upstream.collect(shared)
            }
            else -> {
                // other & custom strategies
                started.command(shared.subscriptionCount)
                    .distinctUntilChanged() // only changes in command have effect
                    .collectLatest { // cancels block on new emission
                        when (it) {
                            SharingCommand.START -> upstream.collect(shared) // can be cancelled
                            SharingCommand.STOP -> { /* just cancel and do nothing else */ }
                            SharingCommand.STOP_AND_RESET_REPLAY_CACHE -> {
                                if (initialValue === NO_VALUE) {
                                    shared.resetReplayCache() // regular shared flow -> reset cache
                                } else {
                                    shared.tryEmit(initialValue) // state flow -> reset to initial value
                                }
                            }
                        }
                    }
            }
        }
    }
}

// -------------------------------- stateIn --------------------------------

/**
 * Converts a _cold_ [Flow] into a _hot_ [StateFlow] that is started in the given coroutine [scope],
 * sharing the most recently emitted value from a single running instance of the upstream flow with multiple
 * downstream subscribers. See the [StateFlow] documentation for the general concepts of state flows.
 *
 * The starting of the sharing coroutine is controlled by the [started] parameter, as explained in the
 * documentation for [shareIn] operator.
 *
 * The `stateIn` operator is useful in situations when there is a _cold_ flow that provides updates to the
 * value of some state and is expensive to create and/or to maintain, but there are multiple subscribers
 * that need to collect the most recent state value. For example, consider a
 * flow of state updates coming from a backend over the expensive network connection, taking a lot of
 * time to establish. Conceptually it might be implemented like this:
 *
 * ```
 * val backendState: Flow<State> = flow {
 *     connectToBackend() // takes a lot of time
 *     try {
 *       while (true) {
 *           emit(receiveStateUpdateFromBackend())
 *       }
 *     } finally {
 *         disconnectFromBackend()
 *     }
 * }
 * ```
 *
 * If this flow is directly used in the application, then every time it is collected a fresh connection is
 * established, and it will take a while before state updates start flowing. However, we can share a single connection
 * and establish it eagerly like this:
 *
 * ```
 * val state: StateFlow<State> = backendMessages.stateIn(scope, SharingStarted.Eagerly, State.LOADING)
 * ```
 *
 * Now, a single connection is shared between all collectors from `state`, and there is a chance that the connection
 * is already established by the time it is needed.
 *
 * ### Upstream completion and error handling
 *
 * **Normal completion of the upstream flow has no effect on subscribers**, and the sharing coroutine continues to run. If a
 * a strategy like [SharingStarted.WhileSubscribed] is used, then the upstream can get restarted again. If a special
 * action on upstream completion is needed, then an [onCompletion] operator can be used before
 * the `stateIn` operator to emit a special value in this case. See the [shareIn] operator's documentation for an example.
 *
 * Any exception in the upstream flow terminates the sharing coroutine without affecting any of the subscribers,
 * and will be handled by the [scope] in which the sharing coroutine is launched. Custom exception handling
 * can be configured by using the [catch] or [retry] operators before the `stateIn` operator, similarly to
 * the [shareIn] operator.
 *
 * ### Operator fusion
 *
 * Application of [flowOn][Flow.flowOn], [conflate][Flow.conflate],
 * [buffer] with [CONFLATED][Channel.CONFLATED] or [RENDEZVOUS][Channel.RENDEZVOUS] capacity,
 * [distinctUntilChanged][Flow.distinctUntilChanged], or [cancellable] operators to a state flow has no effect.
 *
 * @param scope the coroutine scope in which sharing is started.
 * @param started the strategy that controls when sharing is started and stopped.
 * @param initialValue the initial value of the state flow.
 *   This value is also used when the state flow is reset using the [SharingStarted.WhileSubscribed] strategy
 *   with the `replayExpirationMillis` parameter.
 */
public fun <T> Flow<T>.stateIn(
    scope: CoroutineScope,
    started: SharingStarted,
    initialValue: T
): StateFlow<T> {
    val config = configureSharing(1)
    val state = MutableStateFlow(initialValue)
    val job = scope.launchSharing(config.context, config.upstream, state, started, initialValue)
    return ReadonlyStateFlow(state, job)
}

/**
 * Starts the upstream flow in a given [scope], suspends until the first value is emitted, and returns a _hot_
 * [StateFlow] of future emissions, sharing the most recently emitted value from this running instance of the upstream flow
 * with multiple downstream subscribers. See the [StateFlow] documentation for the general concepts of state flows.
 *
 * @param scope the coroutine scope in which sharing is started.
 */
public suspend fun <T> Flow<T>.stateIn(scope: CoroutineScope): StateFlow<T> {
    val config = configureSharing(1)
    val result = CompletableDeferred<StateFlow<T>>()
    scope.launchSharingDeferred(config.context, config.upstream, result)
    return result.await()
}

private fun <T> CoroutineScope.launchSharingDeferred(
    context: CoroutineContext,
    upstream: Flow<T>,
    result: CompletableDeferred<StateFlow<T>>
) {
    launch(context) {
        try {
            var state: MutableStateFlow<T>? = null
            upstream.collect { value ->
                state?.let { it.value = value } ?: run {
                    state = MutableStateFlow(value).also {
                        result.complete(ReadonlyStateFlow(it, coroutineContext.job))
                    }
                }
            }
        } catch (e: Throwable) {
            // Notify the waiter that the flow has failed
            result.completeExceptionally(e)
            // But still cancel the scope where state was (not) produced
            throw e
        }
    }
}

// -------------------------------- asSharedFlow/asStateFlow --------------------------------

/**
 * Represents this mutable shared flow as a read-only shared flow.
 */
public fun <T> MutableSharedFlow<T>.asSharedFlow(): SharedFlow<T> =
    ReadonlySharedFlow(this, null)

/**
 * Represents this mutable state flow as a read-only state flow.
 */
public fun <T> MutableStateFlow<T>.asStateFlow(): StateFlow<T> =
    ReadonlyStateFlow(this, null)

private class ReadonlySharedFlow<T>(
    flow: SharedFlow<T>,
    @Suppress("unused")
    private val job: Job? // keeps a strong reference to the job (if present)
) : SharedFlow<T> by flow, CancellableFlow<T>, FusibleFlow<T> {
    override fun fuse(context: CoroutineContext, capacity: Int, onBufferOverflow: BufferOverflow) =
        fuseSharedFlow(context, capacity, onBufferOverflow)
}

private class ReadonlyStateFlow<T>(
    flow: StateFlow<T>,
    @Suppress("unused")
    private val job: Job? // keeps a strong reference to the job (if present)
) : StateFlow<T> by flow, CancellableFlow<T>, FusibleFlow<T> {
    override fun fuse(context: CoroutineContext, capacity: Int, onBufferOverflow: BufferOverflow) =
        fuseStateFlow(context, capacity, onBufferOverflow)
}

// -------------------------------- onSubscription --------------------------------

/**
 * Returns a flow that invokes the given [action] **after** this shared flow starts to be collected
 * (after the subscription is registered).
 *
 * The [action] is called before any value is emitted from the upstream
 * flow to this subscription but after the subscription is established. It is guaranteed that all emissions to
 * the upstream flow that happen inside or immediately after this `onSubscription` action will be
 * collected by this subscription.
 *
 * The receiver of the [action] is [FlowCollector], so `onSubscription` can emit additional elements.
 */
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
        val safeCollector = SafeCollector(collector, currentCoroutineContext())
        try {
            safeCollector.action()
        } finally {
            safeCollector.releaseIntercepted()
        }
        if (collector is SubscribedFlowCollector) collector.onSubscription()
    }
}
