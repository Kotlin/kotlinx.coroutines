@file:Suppress("UNCHECKED_CAST")

package kotlinx.coroutines.internal

import kotlinx.coroutines.Async
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*

/**
 * Used by debugger-agent to support asynchronous stack traces
 * in sharedFlow, stateFlow, channelFlow, channel, channelIterator.
 */

internal fun collectStacktrace(sharedFlow: SharedFlow<*>, index: Long) =
    collectStacktraceHelperSharedFlow(listOf(sharedFlow, index).hashCode())
internal fun collectStacktraceHelperSharedFlow(@Async.Schedule hash: Int) = Unit

internal fun matchStacktrace(sharedFlow: SharedFlow<*>, index: Long) =
    matchStacktraceHelperSharedFlow(listOf(sharedFlow, index).hashCode())
internal fun matchStacktraceHelperSharedFlow(@Async.Execute hash: Int) = Unit

internal fun dropStacktrace(sharedFlow: SharedFlow<*>, index: Long) = Unit


internal fun <T> collectStacktrace(stateFlow: StateFlow<T>, state: T) =
//    collectStacktraceHelperStateFlow(listOf(stateFlow, state).hashCode())
    collectStacktraceHelperStateFlow(777)
internal fun collectStacktraceHelperStateFlow(@Async.Schedule hash: Int) = Unit

internal fun <T> matchStacktrace(stateFlow: StateFlow<T>, state: T): T {
//    matchStacktraceHelperStateFlow(listOf(stateFlow, state).hashCode())
    matchStacktraceHelperStateFlow(777)
    return state
}
internal fun matchStacktraceHelperStateFlow(@Async.Execute hash: Int) = Unit

internal fun <T> dropStacktrace(stateFlow: StateFlow<T>, state: T): Any? = null


internal fun collectStacktrace(channel: Channel<*>, segment: ChannelSegment<*>, index: Int): Any? = null
//internal fun dropStacktrace(channel: Channel<*>, segment: ChannelSegment<*>, index: Int): Any? = null
internal fun matchStacktrace(channel: Channel<*>, segment: ChannelSegment<*>, index: Int): Any? = null

internal fun sched(@Async.Schedule hash: Int) = Unit
internal fun <T> exec(value: T, @Async.Execute hash: Int) = value
