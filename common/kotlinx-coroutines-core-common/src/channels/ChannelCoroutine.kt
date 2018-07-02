/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*

internal open class ChannelCoroutine<E>(
    parentContext: CoroutineContext,
    protected val _channel: Channel<E>,
    active: Boolean
) : AbstractCoroutine<Unit>(parentContext, active), Channel<E> by _channel {
    val channel: Channel<E>
        get() = this

    // Workaround for KT-23094
    override suspend fun receive(): E = _channel.receive()

    override suspend fun send(element: E) = _channel.send(element)

    override suspend fun receiveOrNull(): E? = _channel.receiveOrNull()

    override fun cancel(cause: Throwable?): Boolean = super.cancel(cause)
}
