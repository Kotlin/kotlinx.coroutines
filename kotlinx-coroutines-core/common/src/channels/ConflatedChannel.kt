/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.internal.*

/**
 * Channel that buffers at most one element and conflates all subsequent `send` and `trySend` invocations,
 * so that the receiver always gets the most recently sent element.
 * Back-to-send sent elements are _conflated_ -- only the most recently sent element is received,
 * while previously sent elements **are lost**.
 * Sender to this channel never suspends and [trySend] always succeeds.
 *
 * This channel is created by `Channel(Channel.CONFLATED)` factory function invocation.
 */
internal open class ConflatedChannel<E>(onUndeliveredElement: OnUndeliveredElement<E>?)
    : ArrayChannel<E>(capacity = 1, onBufferOverflow = BufferOverflow.DROP_OLDEST, onUndeliveredElement = onUndeliveredElement)
