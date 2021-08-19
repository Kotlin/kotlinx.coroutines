/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.internal.*

/**
 * Channel with linked-list buffer of a unlimited capacity (limited only by available memory).
 * Sender to this channel never suspends and [trySend] always succeeds.
 *
 * This channel is created by `Channel(Channel.UNLIMITED)` factory function invocation.
 *
 * This implementation is non-blocking.
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
internal open class LinkedListChannel<E>(onUndeliveredElement: OnUndeliveredElement<E>?)
    : BufferedChannel<E>(capacity = Channel.UNLIMITED, onUndeliveredElement = onUndeliveredElement)

