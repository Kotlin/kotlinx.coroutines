/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.internal.SafeCollector
import kotlin.coroutines.*
import kotlin.jvm.*

public fun <T> Flow<T>.shareIn(
    scope: CoroutineScope,
    replay: Int,
    started: SharingStarted = SharingStarted.Eagerly,
    initialValue: T = NO_VALUE as T
): SharedFlow<T> {
    val shared = MutableSharedFlow<T>(
        bufferCapacity = maxOf(Channel.CHANNEL_DEFAULT_CAPACITY, replay),
        replayCapacity = replay,
        initialValue = initialValue
    )
    scope.launchSharing(this, shared, started)
    return shared
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
        public val Eagerly: SharingStarted = object : SharingStarted {
            override fun commandFlow(subscriptionCount: StateFlow<Int>): Flow<SharingCommand> =
                MutableStateFlow(SharingCommand.START)
        }
        public val Lazily: SharingStarted = TODO()
        public val WhileSubscribed: SharingStarted = TODO()
        public fun WhileSubscribed(stopTimeoutMillis: Long = 0, cacheExpirationMillis: Long = 0): SharingStarted = TODO()
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
    flow.shareIn(scope, 0, SharingStarted.WhileSubscribed(stopTimeoutMillis = 1000L)) // refCount with timeout
    // State sharing
    flow.shareIn(scope, 1) // Eager connect
    flow.shareIn(scope, 1, SharingStarted.Lazily) // Lazy auto-connect
    flow.shareIn(scope, 1, SharingStarted.WhileSubscribed) // refCount
    flow.shareIn(scope, 1, SharingStarted.WhileSubscribed(stopTimeoutMillis = 1000L)) // refCount with timeout
    flow.shareIn(scope, 1, SharingStarted.WhileSubscribed(cacheExpirationMillis = 1000L)) // refCount with expiration
    flow.shareIn(scope, 1, SharingStarted.WhileSubscribed, initialValue = null) // refCount with initial value
    // Log sharing (cache last 100)
    flow.shareIn(scope, 100) // Eager connect
    flow.shareIn(scope, 100, SharingStarted.Lazily) // Lazy auto-connect
    flow.shareIn(scope, 100, SharingStarted.WhileSubscribed) // refCount
    flow.shareIn(scope, 100, SharingStarted.WhileSubscribed(stopTimeoutMillis = 1000L)) // refCount with timeout
    flow.shareIn(scope, 100, SharingStarted.WhileSubscribed(cacheExpirationMillis = 1000L)) // refCount with expiration
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

