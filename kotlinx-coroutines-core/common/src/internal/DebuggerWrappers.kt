@file:Suppress("UNCHECKED_CAST")

package kotlinx.coroutines.internal

import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlin.coroutines.*

/**
 * Used by debugger-agent to support asynchronous stack traces
 * in sharedFlow, stateFlow, channelFlow, channel, channelIterator.
 */

@IgnorableReturnValue
internal fun collectStacktrace(sharedFlow: SharedFlow<*>, index: Long, continuation: Continuation<*>?): Any? = null
@IgnorableReturnValue
internal fun dropStacktrace(sharedFlow: SharedFlow<*>, index: Long): Any? = null
@IgnorableReturnValue
internal fun matchStacktrace(sharedFlow: SharedFlow<*>, index: Long): Any? = null

@IgnorableReturnValue
internal fun <T> collectStacktrace(stateFlow: StateFlow<T>, state: T, continuation: Continuation<*>? = null): Any? = null
internal fun <T> matchStacktrace(stateFlow: StateFlow<T>, state: T): T = state
@IgnorableReturnValue
internal fun <T> dropStacktrace(stateFlow: StateFlow<T>, state: T): Any? = null

@IgnorableReturnValue
internal fun collectStacktrace(segment: ChannelSegment<*>, index: Int, continuation: Continuation<*>?): Any? = null
//internal fun dropStacktrace(segment: ChannelSegment<*>, index: Int): Any? = null
@IgnorableReturnValue
internal fun matchStacktrace(segment: ChannelSegment<*>, index: Int): Any? = null
