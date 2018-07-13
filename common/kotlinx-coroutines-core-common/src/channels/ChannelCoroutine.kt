/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.coroutines.*

internal open class ChannelCoroutine<E>(
    parentContext: CoroutineContext,
    protected val _channel: Channel<E>,
    active: Boolean
) : AbstractCoroutine<Unit>(parentContext, active), Channel<E> by _channel {
    val channel: Channel<E> get() = this

    override fun cancel(cause: Throwable?): Boolean = super.cancel(cause)
}
