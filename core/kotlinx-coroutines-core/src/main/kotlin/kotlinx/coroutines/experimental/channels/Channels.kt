/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.runBlocking

internal const val DEFAULT_CLOSE_MESSAGE = "Channel was closed"

/**
 * Performs the given [action] for each received element.
 */
public inline suspend fun <E> ReceiveChannel<E>.consumeEach(action: (E) -> Unit) {
    for (element in this) action(element)
}

/**
 * @suppress: **Deprecated**: binary compatibility with old code
 */
@Deprecated("binary compatibility with old code", level = DeprecationLevel.HIDDEN)
public suspend fun <E> ReceiveChannel<E>.consumeEach(action: suspend (E) -> Unit) =
    consumeEach { action(it) }

/**
 * Subscribes to this [BroadcastChannel] and performs the specified action for each received element.
 */
public inline suspend fun <E> BroadcastChannel<E>.consumeEach(action: (E) -> Unit) {
    openSubscription().use { channel ->
        for (x in channel) action(x)
    }
}

/**
 * @suppress: **Deprecated**: binary compatibility with old code
 */
@Deprecated("binary compatibility with old code", level = DeprecationLevel.HIDDEN)
public suspend fun <E> BroadcastChannel<E>.consumeEach(action: suspend (E) -> Unit) =
    consumeEach { action(it) }

/**
 * Adds [element] into to this channel, **blocking** the caller while this channel [Channel.isFull],
 * or throws exception if the channel [Channel.isClosedForSend] (see [Channel.close] for details).
 *
 * This is a way to call [Channel.send] method inside a blocking code using [runBlocking],
 * so this function should not be used from coroutine.
 */
public fun <E> SendChannel<E>.sendBlocking(element: E) {
    // fast path
    if (offer(element))
        return
    // slow path
    runBlocking {
        send(element)
    }
}
