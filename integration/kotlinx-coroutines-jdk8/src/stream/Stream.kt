/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.stream

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import java.util.stream.*

/**
 * Represents the given stream as a flow and [closes][Stream.close] the stream afterwards.
 * The resulting flow can be [collected][Flow.collect] only once
 * and throws [IllegalStateException] when trying to collect it more than once.
 */
public fun <T> Stream<T>.consumeAsFlow(): Flow<T> = StreamFlow(this)

private class StreamFlow<T>(private val stream: Stream<T>) : Flow<T> {
    private val consumed = atomic(false)

    @InternalCoroutinesApi
    override suspend fun collect(collector: FlowCollector<T>) {
        if (!consumed.compareAndSet(false, true)) error("Stream.consumeAsFlow can be collected only once")
        try {
            for (value in stream.iterator()) {
                collector.emit(value)
            }
        } finally {
            stream.close()
        }
    }
}
