@file:Suppress("UNCHECKED_CAST")

package kotlinx.coroutines.internal

import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*

/**
 * Used by debugger-agent to support asynchronous stack traces
 * in sharedFlow, stateFlow, channelFlow, channel, channelIterator.
 */

internal fun collectStacktrace(sharedFlow: SharedFlow<*>, index: Long): Any? = null
internal fun dropStacktrace(sharedFlow: SharedFlow<*>, index: Long): Any? = null
internal fun matchStacktrace(sharedFlow: SharedFlow<*>, index: Long): Any? = null

internal fun <T> collectStacktrace(stateFlow: StateFlow<T>, state: T): Any? = null
internal fun <T> matchStacktrace(stateFlow: StateFlow<T>, state: T): T = state
internal fun <T> dropStacktrace(stateFlow: StateFlow<T>, state: T): Any? = null

internal fun collectStacktrace(segment: ChannelSegment<*>, index: Int): Any? = null
//internal fun dropStacktrace(segment: ChannelSegment<*>, index: Int): Any? = null
internal fun matchStacktrace(segment: ChannelSegment<*>, index: Int): Any? = null
