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
    start: SharingStart = SharingStart.Eager,
    cache: SharingCache<T> = SharingCache.None
): SharedFlow<T> {
    val upstreamFlow = this
    val sharedFlow = cache.createMutableSharedFlow<T>()
    scope.launch { // the single coroutine to rule the sharing
        try {
            start.commandFlow(sharedFlow.collectorsCount)
                .distinctUntilChanged()
                .collectLatest { // cancels block on new emission
                    when (it) {
                        SharingCommand.START -> upstreamFlow.collect(sharedFlow) // can be cancelled
                        SharingCommand.STOP -> {} // just cancel collection and do nothing else
                        SharingCommand.RESET_CACHE -> sharedFlow.resetBuffer()
                    }
                }
        } finally {
            sharedFlow.resetBuffer() // on any completion/cancellation/failure of sharing
        }
    }
    return sharedFlow
}

public fun <T> Flow<T>.stateIn(
    scope: CoroutineScope,
    start: SharingStart = SharingStart.Eager,
    initialValue: T
): StateFlow<T> {
    TODO()
}

public suspend fun <T> Flow<T>.stateIn(scope: CoroutineScope): StateFlow<T> = TODO()

public interface SharingStart {
    public companion object {
        public val Eager: SharingStart = TODO()
        public val Lazy: SharingStart = TODO()
        public val OnDemand: SharingStart = TODO()
        public fun OnDemand(stopTimeout: Long = 0, cacheExpiration: Long = 0): SharingStart = TODO()
    }

    public fun commandFlow(numberOfCollectors: StateFlow<Int>): Flow<SharingCommand>
}

public enum class SharingCommand { START, STOP, RESET_CACHE }

public sealed class SharingCache<out V> {
    public companion object {
        public val None: SharingCache<Nothing> = TODO()
        public val Last: SharingCache<Nothing> = TODO()
        public fun Last(replaySize: Int): SharingCache<Nothing> = TODO()
        public fun <V> Last(replaySize: Int = 1, initialValue: V): SharingCache<V> = TODO()
    }
}

public fun <T> SharingCache<T>.createMutableSharedFlow(): MutableSharedFlow<T> = TODO()

public fun SharingStart.Companion.Lazy(waitNumberOfCollectors: Int): SharingStart = object : SharingStart {
    override fun commandFlow(numberOfCollectors: StateFlow<Int>) =
        numberOfCollectors
            .map { if (it >= waitNumberOfCollectors) SharingCommand.START else SharingCommand.STOP }
            .distinctUntilChanged { old, new -> old == SharingCommand.START } // keep START once it is there
}

// test
public fun main() {
    val flow: Flow<Int> = flowOf(42)
    val scope: CoroutineScope = GlobalScope

    // Basic event sharing
    flow.shareIn(scope) // Eager connect
    flow.shareIn(scope, SharingStart.Lazy) // Lazy auto-connect
    flow.shareIn(scope, SharingStart.OnDemand) // refCount
    flow.shareIn(scope, SharingStart.OnDemand(stopTimeout = 1000L)) // refCount with timeout
    // State sharing
    flow.shareIn(scope, cache = SharingCache.Last) // Eager connect
    flow.shareIn(scope, SharingStart.Lazy, SharingCache.Last) // Lazy auto-connect
    flow.shareIn(scope, SharingStart.OnDemand, SharingCache.Last) // refCount
    flow.shareIn(scope, SharingStart.OnDemand(stopTimeout = 1000L), SharingCache.Last) // refCount with timeout
    flow.shareIn(scope, SharingStart.OnDemand(cacheExpiration = 1000L), SharingCache.Last) // refCount with expiration
    flow.shareIn(scope, SharingStart.OnDemand, SharingCache.Last(initialValue = null)) // refCount with initial value
    // Log sharing (cache last 100)
    flow.shareIn(scope, cache = SharingCache.Last(100)) // Eager connect
    flow.shareIn(scope, SharingStart.Lazy, SharingCache.Last(100)) // Lazy auto-connect
    flow.shareIn(scope, SharingStart.OnDemand, SharingCache.Last(100)) // refCount
    flow.shareIn(scope, SharingStart.OnDemand(stopTimeout = 1000L), SharingCache.Last(100)) // refCount with timeout
    flow.shareIn(scope, SharingStart.OnDemand(cacheExpiration = 1000L), SharingCache.Last(100)) // refCount with expiration

    val ss = SharingCache.Last(initialValue = "OK")
//    ss.createMutableSharedFlow<Int>() // ERROR!
    ss.createMutableSharedFlow<String>()
    ss.createMutableSharedFlow<String?>()
    ss.createMutableSharedFlow<Any?>()
    val ff = flow.shareIn(scope, cache = ss)
}
