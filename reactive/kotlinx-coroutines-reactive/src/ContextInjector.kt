/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.coroutines.InternalCoroutinesApi
import org.reactivestreams.Publisher
import kotlin.coroutines.CoroutineContext

/** @suppress */
@InternalCoroutinesApi
public interface ContextInjector {
    /**
     * Injects `ReactorContext` element from the given context into the `SubscriberContext` of the publisher.
     * This API used as an indirection layer between `reactive` and `reactor` modules.
     */
    public fun <T> injectCoroutineContext(publisher: Publisher<T>, coroutineContext: CoroutineContext): Publisher<T>
}
