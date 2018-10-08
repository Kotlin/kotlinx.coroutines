/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels8

import kotlinx.coroutines.channels.*
import java.util.function.*
import java.util.stream.*

/**
 * Applies the [collector] to the [ReceiveChannel]
 */
@Deprecated("No replacement")
public suspend fun <T, A : Any, R> ReceiveChannel<T>.collect(collector: Collector<T, A, R>): R {
    val container: A = collector.supplier().get()
    val accumulator: BiConsumer<A, T> = collector.accumulator()
    consumeEach { accumulator.accept(container, it) }
    return collector.finisher().apply(container)
}