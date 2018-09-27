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
    override val cancelsParent: Boolean get() = true

    val channel: Channel<E> get() = this

    override fun cancel() = cancel(null)

    override fun cancel(cause: Throwable?): Boolean {
        val wasCancelled = _channel.cancel(cause)
        if (wasCancelled) super.cancel(cause) // cancel the job
        return wasCancelled
    }
}
