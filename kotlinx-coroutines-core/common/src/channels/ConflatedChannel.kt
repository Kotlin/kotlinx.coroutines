/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.internal.SegmentQueueSynchronizer
import kotlinx.coroutines.selects.*

/**
 * Channel that buffers at most one element and conflates all subsequent `send` and `offer` invocations,
 * so that the receiver always gets the most recently sent element.
 * Back-to-send sent elements are _conflated_ -- only the the most recently sent element is received,
 * while previously sent elements **are lost**.
 * Sender to this channel never suspends and [offer] always returns `true`.
 *
 * This channel is created by `Channel(Channel.CONFLATED)` factory function invocation.
 *
 * This implementation is fully lock-free.
 */
internal open class ConflatedChannel<E>: AbstractChannel<E>(), Channel<E> {
    private val sync = SegmentQueueSynchronizer<ConflatedChannel<E>, E>() // TODO lazy initialization
    private val value = atomic<Any?>(NO_VALUE)
    private val waiters = atomic(0) // -1 if this channel contains an element;

    override fun offerInternal(element: E): Any {
        waiters.loop { w ->
            when (w) {
                -1 -> {
                    // do not change waiters, update the value
                    val curValue = value.value
                    if (curValue === NO_VALUE) return@loop // todo: spin wait, fix by dcss
                    // if this CAS fails then another `send` came earlier
                    value.compareAndSet(curValue, element)
                    return SUCCESS_RESULT
                }
                0 -> {
                    // inc waiters
                    if (!waiters.compareAndSet(w, w - 1)) return@loop
                    // set the element, if this CAS fails then another `send` came earlier
                    value.compareAndSet(NO_VALUE, element)
                    return SUCCESS_RESULT
                }
                else -> {
                    // decrement the number of waiters
                    if (!waiters.compareAndSet(w, w - 1)) return@loop
                    sync.resumeNextWaiter(element)
                    return SUCCESS_RESULT
                }
            }
        }
    }

    override suspend fun sendInternal(element: E): Any = offerInternal(element)

    override fun pollInternal(): Any? {
        waiters.loop { w ->
            when (w) {
                -1 -> {
                    if (!waiters.compareAndSet(-1, 0)) return@loop
                    value.loop { v ->
                        // todo: spin loop here
                        if (v !== NO_VALUE && value.compareAndSet(v, NO_VALUE)) return v
                    }
                }
                else -> return POLL_FAILED
            }
        }
    }

    override suspend fun receiveInternal(): Any? {
        waiters.loop { w ->
            when (w) {
                -1 -> {
                    if (!waiters.compareAndSet(-1, 0)) return@loop
                    value.loop { v ->
                        // todo: spin loop here
                        if (v !== NO_VALUE && value.compareAndSet(v, NO_VALUE)) return v
                    }
                }
                else -> {
                    if (!waiters.compareAndSet(w, w + 1)) return@loop
                    return sync.suspend(this, ::onCancellation)
                }
            }
        }
    }

    override fun helpCloseIdempotent(wasClosed: Boolean) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun helpCancelIdempotent(wasClosed: Boolean) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    companion object {
        private fun onCancellation(c: ConflatedChannel<*>) {}

    }

    @ExperimentalCoroutinesApi
    override val isFull: Boolean get() = false
    @ExperimentalCoroutinesApi
    override val isEmpty: Boolean get() = waiters.value != -1

    override val onSend: SelectClause2<E, SendChannel<E>> get() = TODO("not implemented")
    override val onReceive: SelectClause1<E> get() = TODO("not implemented")
    @ObsoleteCoroutinesApi
    override val onReceiveOrNull: SelectClause1<E?> get() = TODO("not implemented")
    @InternalCoroutinesApi
    override val onReceiveOrClosed: SelectClause1<ValueOrClosed<E>> get() = TODO("not implemented")
}

private val NO_VALUE = Symbol("NO_VALUE")