/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.coroutines.*

@Suppress("DEPRECATION")
internal open class ChannelCoroutine<E>(
    parentContext: CoroutineContext,
    protected val _channel: Channel<E>,
    active: Boolean
) : AbstractCoroutine<Unit>(parentContext, active), Channel<E> by _channel {
    val channel: Channel<E> get() = this

    override fun cancel() {
        cancelInternal(null)
    }

    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.2.0, binary compatibility with versions <= 1.1.x")
    final override fun cancel(cause: Throwable?): Boolean =
        cancelInternal(cause)

    final override fun cancel(cause: CancellationException?) {
        cancelInternal(cause)
    }

    override fun cancelInternal(cause: Throwable?): Boolean {
        _channel.cancel(cause?.toCancellationException()) // cancel the channel
        cancelCoroutine(cause) // cancel the job
        return true // does not matter - result is used in DEPRECATED functions only
    }
}
