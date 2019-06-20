/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.channels.ArrayChannel
import kotlinx.coroutines.flow.*

internal fun <T> FlowCollector<T>.asConcurrentFlowCollector(): ConcurrentFlowCollector<T> =
    this as? ConcurrentFlowCollector<T> ?: SerializingCollector(this)

// Flow collector that supports concurrent emit calls.
// It is internal for now but may be public in the future.
// Two basic implementations are here: SendingCollector and ConcurrentFlowCollector
internal interface ConcurrentFlowCollector<T> : FlowCollector<T>

/**
 * Collection that sends to channel. It is marked as [ConcurrentFlowCollector] because it can be used concurrently.
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public class SendingCollector<T>(
    private val channel: SendChannel<T>
) : ConcurrentFlowCollector<T> {
    override suspend fun emit(value: T) = channel.send(value)
}

// Effectively serializes access to downstream collector for merging
// This is basically a converted from FlowCollector interface to ConcurrentFlowCollector
private class SerializingCollector<T>(
    private val downstream: FlowCollector<T>
) : ConcurrentFlowCollector<T> {
    // Let's try to leverage the fact that merge is never contended
    // Should be Any, but KT-30796
    private val _channel = atomic<ArrayChannel<Any?>?>(null)
    private val inProgressLock = atomic(false)

    private val channel: ArrayChannel<Any?>
        get() = _channel.updateAndGet { value ->
            if (value != null) return value
            ArrayChannel(Channel.CHANNEL_DEFAULT_CAPACITY)
        }!!

    public override suspend fun emit(value: T) {
        if (!inProgressLock.tryAcquire()) {
            channel.send(value ?: NULL)
            if (inProgressLock.tryAcquire()) {
                helpEmit()
            }
            return
        }
        downstream.emit(value)
        helpEmit()
    }

    @Suppress("UNCHECKED_CAST")
    private suspend fun helpEmit() {
        while (true) {
            while (true) {
                val element = _channel.value?.poll() ?: break // todo: pollOrClosed
                downstream.emit(NULL.unbox(element))
            }
            inProgressLock.release()
            // Enforce liveness
            if (_channel.value?.isEmpty != false || !inProgressLock.tryAcquire()) break
        }
    }
}

@Suppress("NOTHING_TO_INLINE")
private inline fun AtomicBoolean.tryAcquire(): Boolean = compareAndSet(false, true)

@Suppress("NOTHING_TO_INLINE")
private inline fun AtomicBoolean.release() {
    value = false
}
