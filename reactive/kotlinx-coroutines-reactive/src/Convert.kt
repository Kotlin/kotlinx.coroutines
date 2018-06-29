/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.reactive

import kotlinx.coroutines.experimental.DefaultDispatcher
import kotlinx.coroutines.experimental.channels.ReceiveChannel
import org.reactivestreams.Publisher
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Converts a stream of elements received from the channel to the hot reactive publisher.
 *
 * Every subscriber receives values from this channel in **fan-out** fashion. If the are multiple subscribers,
 * they'll receive values in round-robin way.
 *
 * @param context -- the coroutine context from which the resulting observable is going to be signalled
 */
public fun <T> ReceiveChannel<T>.asPublisher(context: CoroutineContext = DefaultDispatcher): Publisher<T> = publish(context) {
    for (t in this@asPublisher)
        send(t)
}

/**
 * @suppress **Deprecated**: Renamed to [asPublisher]
 */
@Deprecated(message = "Renamed to `asPublisher`",
    replaceWith = ReplaceWith("asPublisher(context)"))
public fun <T> ReceiveChannel<T>.toPublisher(context: CoroutineContext): Publisher<T> = asPublisher(context)