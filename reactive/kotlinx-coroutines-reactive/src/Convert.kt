/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.coroutines.channels.*
import org.reactivestreams.*
import kotlin.coroutines.*

/** @suppress */
@Deprecated(message = "Deprecated in the favour of consumeAsFlow()",
    level = DeprecationLevel.HIDDEN, // Error in 1.4, HIDDEN in 1.6.0
    replaceWith = ReplaceWith("this.consumeAsFlow().asPublisher(context)", imports = ["kotlinx.coroutines.flow.consumeAsFlow"]))
public fun <T> ReceiveChannel<T>.asPublisher(context: CoroutineContext = EmptyCoroutineContext): Publisher<T> = publish(context) {
    for (t in this@asPublisher)
        send(t)
}
