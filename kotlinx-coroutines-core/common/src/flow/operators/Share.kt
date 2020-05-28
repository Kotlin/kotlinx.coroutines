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

public fun <T> Flow<T>.stateIn(
    scope: CoroutineScope,
    started: SharingStarted = SharingStarted.Eagerly,
    initialValue: T
): StateFlow<T> {
    val state = MutableStateFlow(initialValue)
    scope.launchSharing(this, state, started)
    return state.asStateFlow()
}

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

@ExperimentalCoroutinesApi
public fun <T> MutableSharedFlow<T>.asSharedFlow(): SharedFlow<T> =
    object : SharedFlow<T> by this {}

@ExperimentalCoroutinesApi
public fun <T> MutableStateFlow<T>.asStateFlow(): StateFlow<T> =
    object : StateFlow<T> by this {}

// -------------------------------- onSubscription --------------------------------

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

