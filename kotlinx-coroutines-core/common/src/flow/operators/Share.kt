/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.internal.SafeCollector
import kotlin.coroutines.*
import kotlin.jvm.*

public fun <T> Flow<T>.shareIn(
    scope: CoroutineScope,
    replay: Int,
    started: SharingStarted = SharingStarted.Eagerly,
    initialValue: T = NO_VALUE as T
): SharedFlow<T> {
    val shared = MutableSharedFlow<T>(replay, initialValue = initialValue)
    scope.launchSharing(this, shared, started)
    return shared
}

private fun <T> CoroutineScope.launchSharing(upstream: Flow<T>, shared: MutableSharedFlow<T>, started: SharingStarted) {
    launch { // the single coroutine to rule the sharing
        try {
            started.commandFlow(shared.subscriptionCount)
                .distinctUntilChanged()
                .collectLatest { // cancels block on new emission
                    when (it) {
                        SharingCommand.START -> upstream.collect(shared) // can be cancelled
                        SharingCommand.STOP -> { /* just cancel collection and do nothing else */ }
                        SharingCommand.RESET_BUFFER -> shared.resetBuffer()
                    }
                }
        } finally {
            shared.resetBuffer() // on any completion/cancellation/failure of sharing
        }
    }
}

public fun <T> Flow<T>.stateIn(
    scope: CoroutineScope,
    started: SharingStarted = SharingStarted.Eagerly,
    initialValue: T
): StateFlow<T> {
    val state = MutableStateFlow(initialValue)
    scope.launchSharing(this, state, started)
    return state
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
                    result.complete(it)
                }
            }
        }
    }
}

public interface SharingStarted {
    public companion object {
        public val Eagerly: SharingStarted = TODO()
        public val Lazily: SharingStarted = TODO()
        public val WhileSubscribed: SharingStarted = TODO()
        public fun WhileSubscribed(stopTimeout: Long = 0, cacheExpiration: Long = 0): SharingStarted = TODO()
    }

    public fun commandFlow(subscriptionCount: StateFlow<Int>): Flow<SharingCommand>
}

public enum class SharingCommand { START, STOP, RESET_BUFFER }

public fun SharingStarted.Companion.Lazily(waitSubscribers: Int): SharingStarted = object : SharingStarted {
    override fun commandFlow(subscriptionCount: StateFlow<Int>) =
        subscriptionCount
            .map { if (it >= waitSubscribers) SharingCommand.START else SharingCommand.STOP }
            .distinctUntilChanged { old, new -> old == SharingCommand.START } // keep START once it is there
}

// test
public fun main() {
    val flow: Flow<Int> = flowOf(42)
    val scope: CoroutineScope = GlobalScope

    // Basic event sharing
    flow.shareIn(scope, 0) // Eager connect
    flow.shareIn(scope, 0, SharingStarted.Lazily) // Lazy auto-connect
    flow.shareIn(scope, 0, SharingStarted.WhileSubscribed) // refCount
    flow.shareIn(scope, 0, SharingStarted.WhileSubscribed(stopTimeout = 1000L)) // refCount with timeout
    // State sharing
    flow.shareIn(scope, 1) // Eager connect
    flow.shareIn(scope, 1, SharingStarted.Lazily) // Lazy auto-connect
    flow.shareIn(scope, 1, SharingStarted.WhileSubscribed) // refCount
    flow.shareIn(scope, 1, SharingStarted.WhileSubscribed(stopTimeout = 1000L)) // refCount with timeout
    flow.shareIn(scope, 1, SharingStarted.WhileSubscribed(cacheExpiration = 1000L)) // refCount with expiration
    flow.shareIn(scope, 1, SharingStarted.WhileSubscribed, initialValue = null) // refCount with initial value
    // Log sharing (cache last 100)
    flow.shareIn(scope, 100) // Eager connect
    flow.shareIn(scope, 100, SharingStarted.Lazily) // Lazy auto-connect
    flow.shareIn(scope, 100, SharingStarted.WhileSubscribed) // refCount
    flow.shareIn(scope, 100, SharingStarted.WhileSubscribed(stopTimeout = 1000L)) // refCount with timeout
    flow.shareIn(scope, 100, SharingStarted.WhileSubscribed(cacheExpiration = 1000L)) // refCount with expiration
}

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

