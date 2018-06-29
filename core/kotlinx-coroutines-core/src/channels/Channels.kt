/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("ChannelsKt")

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*

// -------- Operations on SendChannel  --------

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
