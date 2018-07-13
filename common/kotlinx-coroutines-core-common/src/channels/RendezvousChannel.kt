/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*

/**
 * Rendezvous channel. This channel does not have any buffer at all. An element is transferred from sender
 * to receiver only when [send] and [receive] invocations meet in time (rendezvous), so [send] suspends
 * until another coroutine invokes [receive] and [receive] suspends until another coroutine invokes [send].
 *
 * Use `Channel()` factory function to conveniently create an instance of rendezvous channel.
 *
 * This implementation is fully lock-free.
 * 
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public open class RendezvousChannel<E>
@Deprecated(
    "Replace with Channel factory function",
    replaceWith = ReplaceWith("Channel(Channel.RENDEZVOUS)")
)
constructor() : AbstractChannel<E>() {
    protected final override val isBufferAlwaysEmpty: Boolean get() = true
    protected final override val isBufferEmpty: Boolean get() = true
    protected final override val isBufferAlwaysFull: Boolean get() = true
    protected final override val isBufferFull: Boolean get() = true
}
