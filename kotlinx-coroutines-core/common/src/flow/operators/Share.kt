/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.jvm.*

public fun <T> Flow<T>.shareIn(
    scope: CoroutineScope,
    replay: Int = 0,
    start: SharingStart = SharingStart.Eager,
    initialValue: T = NO_VALUE as T
): SharedFlow<T> {
    val sharedFlow = MutableSharedFlow<T>(replay, initialValue = initialValue)
    launchSharing(scope, start, sharedFlow, this)
    return sharedFlow
}

private fun <T> launchSharing(
    scope: CoroutineScope,
    start: SharingStart,
    sharedFlow: MutableSharedFlow<T>,
    upstreamFlow: Flow<T>
) {
    scope.launch { // the single coroutine to rule the sharing
        try {
            start.commandFlow(sharedFlow.collectorCount)
                .distinctUntilChanged()
                .collectLatest { // cancels block on new emission
                    when (it) {
                        SharingCommand.START -> upstreamFlow.collect(sharedFlow) // can be cancelled
                        SharingCommand.STOP -> {
                        } // just cancel collection and do nothing else
                        SharingCommand.RESET_BUFFER -> sharedFlow.resetBuffer()
                    }
                }
        } finally {
            sharedFlow.resetBuffer() // on any completion/cancellation/failure of sharing
        }
    }
}

public fun <T> Flow<T>.stateIn(
    scope: CoroutineScope,
    start: SharingStart = SharingStart.Eager,
    value: T
): StateFlow<T> {
    val stateFlow = MutableStateFlow(value)
    launchSharing(scope, start, stateFlow, this)
    return stateFlow
}

public suspend fun <T> Flow<T>.stateIn(scope: CoroutineScope): StateFlow<T> = TODO()

public interface SharingStart {
    public companion object {
        public val Eager: SharingStart = TODO()
        public val Lazy: SharingStart = TODO()
        public val OnDemand: SharingStart = TODO()
        public fun OnDemand(stopTimeout: Long = 0, cacheExpiration: Long = 0): SharingStart = TODO()
    }

    public fun commandFlow(collectCount: StateFlow<Int>): Flow<SharingCommand>
}

public enum class SharingCommand { START, STOP, RESET_BUFFER }

public fun SharingStart.Companion.Lazy(waitCollectors: Int): SharingStart = object : SharingStart {
    override fun commandFlow(collectCount: StateFlow<Int>) =
        collectCount
            .map { if (it >= waitCollectors) SharingCommand.START else SharingCommand.STOP }
            .distinctUntilChanged { old, new -> old == SharingCommand.START } // keep START once it is there
}

// test
public fun main() {
    val flow: Flow<Int> = flowOf(42)
    val scope: CoroutineScope = GlobalScope

    // Basic event sharing
    flow.shareIn(scope) // Eager connect
    flow.shareIn(scope, 0, SharingStart.Lazy) // Lazy auto-connect
    flow.shareIn(scope, 0, SharingStart.OnDemand) // refCount
    flow.shareIn(scope, 0, SharingStart.OnDemand(stopTimeout = 1000L)) // refCount with timeout
    // State sharing
    flow.shareIn(scope, 1) // Eager connect
    flow.shareIn(scope, 1, SharingStart.Lazy) // Lazy auto-connect
    flow.shareIn(scope, 1, SharingStart.OnDemand) // refCount
    flow.shareIn(scope, 1, SharingStart.OnDemand(stopTimeout = 1000L)) // refCount with timeout
    flow.shareIn(scope, 1, SharingStart.OnDemand(cacheExpiration = 1000L)) // refCount with expiration
    flow.shareIn(scope, 1, SharingStart.OnDemand, initialValue = null) // refCount with initial value
    // Log sharing (cache last 100)
    flow.shareIn(scope, 100) // Eager connect
    flow.shareIn(scope, 100, SharingStart.Lazy) // Lazy auto-connect
    flow.shareIn(scope, 100, SharingStart.OnDemand) // refCount
    flow.shareIn(scope, 100, SharingStart.OnDemand(stopTimeout = 1000L)) // refCount with timeout
    flow.shareIn(scope, 100, SharingStart.OnDemand(cacheExpiration = 1000L)) // refCount with expiration
}
