/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.IgnoreJreRequirement
import kotlin.time.*

/**
 * A command emitted by [SharingStarted] implementations to control the sharing coroutine in
 * the [shareIn] and [stateIn] operators.
 */
public enum class SharingCommand {
    /**
     * Starts sharing, launching collection of the upstream flow.
     *
     * Emitting this command again does not do anything. Emit [STOP] and then [START] to restart an
     * upstream flow.
     */
    START,

    /**
     * Stops sharing, cancelling collection of the upstream flow.
     */
    STOP,

    /**
     * Stops sharing, cancelling collection of the upstream flow, and resets the [SharedFlow.replayCache]
     * to its initial state.
     * The [shareIn] operator calls [MutableSharedFlow.resetReplayCache];
     * the [stateIn] operator resets the value to its original `initialValue`.
     */
    STOP_AND_RESET_REPLAY_CACHE
}

/**
 * A strategy for starting and stopping the sharing coroutine in [shareIn] and [stateIn] operators.
 *
 * This functional interface provides a set of built-in strategies: [Eagerly], [Lazily], [WhileSubscribed], and
 * supports custom strategies by implementing this interface's [command] function.
 *
 * For example, it is possible to define a custom strategy that starts the upstream only when the number
 * of subscribers exceeds the given `threshold` and make it an extension on [SharingStarted.Companion] so
 * that it looks like a built-in strategy on the use-site:
 *
 * ```
 * fun SharingStarted.Companion.WhileSubscribedAtLeast(threshold: Int) =
 *     SharingStarted { subscriptionCount: StateFlow<Int> ->
 *         subscriptionCount.map { if (it >= threshold) SharingCommand.START else SharingCommand.STOP }
 *     }
 * ```
 *
 * ### Commands
 *
 * The `SharingStarted` strategy works by emitting [commands][SharingCommand] that control upstream flow from its
 * [`command`][command] flow implementation function. Back-to-back emissions of the same command have no effect.
 * Only emission of a different command has effect:
 *
 * * [START][SharingCommand.START] &mdash; the upstream flow is started.
 * * [STOP][SharingCommand.STOP] &mdash; the upstream flow is stopped.
 * * [STOP_AND_RESET_REPLAY_CACHE][SharingCommand.STOP_AND_RESET_REPLAY_CACHE] &mdash;
 *   the upstream flow is stopped and the [SharedFlow.replayCache] is reset to its initial state.
 *   The [shareIn] operator calls [MutableSharedFlow.resetReplayCache];
 *   the [stateIn] operator resets the value to its original `initialValue`.
 *   
 * Initially, the upstream flow is stopped and is in the initial state, so the emission of additional
 * [STOP][SharingCommand.STOP] and [STOP_AND_RESET_REPLAY_CACHE][SharingCommand.STOP_AND_RESET_REPLAY_CACHE] commands will
 * have no effect.
 *
 * The completion of the `command` flow normally has no effect (the upstream flow keeps running if it was running).
 * The failure of the `command` flow cancels the sharing coroutine and the upstream flow.
 */
public fun interface SharingStarted {
    public companion object {
        /**
         * Sharing is started immediately and never stops.
         */
        public val Eagerly: SharingStarted = StartedEagerly()

        /**
         * Sharing is started when the first subscriber appears and never stops.
         */
        public val Lazily: SharingStarted = StartedLazily()

        /**
         * Sharing is started when the first subscriber appears, immediately stops when the last
         * subscriber disappears (by default), keeping the replay cache forever (by default).
         *
         * It has the following optional parameters:
         *
         * * [stopTimeoutMillis] &mdash; configures a delay (in milliseconds) between the disappearance of the last
         *   subscriber and the stopping of the sharing coroutine. It defaults to zero (stop immediately).
         * * [replayExpirationMillis] &mdash; configures a delay (in milliseconds) between the stopping of
         *   the sharing coroutine and the resetting of the replay cache (which makes the cache empty for the [shareIn] operator
         *   and resets the cached value to the original `initialValue` for the [stateIn] operator).
         *   It defaults to `Long.MAX_VALUE` (keep replay cache forever, never reset buffer).
         *   Use zero value to expire the cache immediately.
         *
         * This function throws [IllegalArgumentException] when either [stopTimeoutMillis] or [replayExpirationMillis]
         * are negative.
         */
        @Suppress("FunctionName")
        public fun WhileSubscribed(
            stopTimeoutMillis: Long = 0,
            replayExpirationMillis: Long = Long.MAX_VALUE
        ): SharingStarted =
            StartedWhileSubscribed(stopTimeoutMillis, replayExpirationMillis)
    }

    /**
     * Transforms the [subscriptionCount][MutableSharedFlow.subscriptionCount] state of the shared flow into the
     * flow of [commands][SharingCommand] that control the sharing coroutine. See the [SharingStarted] interface
     * documentation for details.
     */
    public fun command(subscriptionCount: StateFlow<Int>): Flow<SharingCommand>
}

/**
 * Sharing is started when the first subscriber appears, immediately stops when the last
 * subscriber disappears (by default), keeping the replay cache forever (by default).
 *
 * It has the following optional parameters:
 *
 * * [stopTimeout] &mdash; configures a delay between the disappearance of the last
 *   subscriber and the stopping of the sharing coroutine. It defaults to zero (stop immediately).
 * * [replayExpiration] &mdash; configures a delay between the stopping of
 *   the sharing coroutine and the resetting of the replay cache (which makes the cache empty for the [shareIn] operator
 *   and resets the cached value to the original `initialValue` for the [stateIn] operator).
 *   It defaults to [Duration.INFINITE] (keep replay cache forever, never reset buffer).
 *   Use [Duration.ZERO] value to expire the cache immediately.
 *
 * This function throws [IllegalArgumentException] when either [stopTimeout] or [replayExpiration]
 * are negative.
 */
@Suppress("FunctionName")
public fun SharingStarted.Companion.WhileSubscribed(
    stopTimeout: Duration = Duration.ZERO,
    replayExpiration: Duration = Duration.INFINITE
): SharingStarted =
    StartedWhileSubscribed(stopTimeout.inWholeMilliseconds, replayExpiration.inWholeMilliseconds)

// -------------------------------- implementation --------------------------------

private class StartedEagerly : SharingStarted {
    override fun command(subscriptionCount: StateFlow<Int>): Flow<SharingCommand> =
        flowOf(SharingCommand.START)
    override fun toString(): String = "SharingStarted.Eagerly"
}

private class StartedLazily : SharingStarted {
    override fun command(subscriptionCount: StateFlow<Int>): Flow<SharingCommand> = flow {
        var started = false
        subscriptionCount.collect { count ->
            if (count > 0 && !started) {
                started = true
                emit(SharingCommand.START)
            }
        }
    }

    override fun toString(): String = "SharingStarted.Lazily"
}

private class StartedWhileSubscribed(
    private val stopTimeout: Long,
    private val replayExpiration: Long
) : SharingStarted {
    init {
        require(stopTimeout >= 0) { "stopTimeout($stopTimeout ms) cannot be negative" }
        require(replayExpiration >= 0) { "replayExpiration($replayExpiration ms) cannot be negative" }
    }

    override fun command(subscriptionCount: StateFlow<Int>): Flow<SharingCommand> = subscriptionCount
        .transformLatest { count ->
            if (count > 0) {
                emit(SharingCommand.START)
            } else {
                delay(stopTimeout)
                if (replayExpiration > 0) {
                    emit(SharingCommand.STOP)
                    delay(replayExpiration)
                }
                emit(SharingCommand.STOP_AND_RESET_REPLAY_CACHE)
            }
        }
        .dropWhile { it != SharingCommand.START } // don't emit any STOP/RESET_BUFFER to start with, only START
        .distinctUntilChanged() // just in case somebody forgets it, don't leak our multiple sending of START

    @OptIn(ExperimentalStdlibApi::class)
    override fun toString(): String {
        val params = buildList(2) {
            if (stopTimeout > 0) add("stopTimeout=${stopTimeout}ms")
            if (replayExpiration < Long.MAX_VALUE) add("replayExpiration=${replayExpiration}ms")
        }
        return "SharingStarted.WhileSubscribed(${params.joinToString()})"
    }

    // equals & hashcode to facilitate testing, not documented in public contract
    override fun equals(other: Any?): Boolean =
        other is StartedWhileSubscribed &&
            stopTimeout == other.stopTimeout &&
            replayExpiration == other.replayExpiration

    @IgnoreJreRequirement // desugared hashcode implementation
    override fun hashCode(): Int = stopTimeout.hashCode() * 31 + replayExpiration.hashCode()
}
