/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.coroutines.channels.*
import org.reactivestreams.*
import kotlin.coroutines.*

/**
 * Converts a stream of elements received from the channel to the hot reactive publisher.
 *
 * Every subscriber receives values from this channel in **fan-out** fashion. If the are multiple subscribers,
 * they'll receive values in round-robin way.
 * @param context -- the coroutine context from which the resulting observable is going to be signalled
 */
@Deprecated(message = "Deprecated in the favour of consumeAsFlow()",
    level = DeprecationLevel.WARNING,
    replaceWith = ReplaceWith("this.consumeAsFlow().asPublisher()"))
public fun <T> ReceiveChannel<T>.asPublisher(context: CoroutineContext = EmptyCoroutineContext): Publisher<T> = publish(context) {
    for (t in this@asPublisher)
        send(t)
}
