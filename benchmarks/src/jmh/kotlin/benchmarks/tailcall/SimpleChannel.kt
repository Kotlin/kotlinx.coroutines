/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.tailcall

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
public abstract class SimpleChannel {
    companion object {
        const val NULL_SURROGATE: Int = -1
    }

    @JvmField
    protected var producer: Continuation<Unit>? = null
    @JvmField
    protected var enqueuedValue: Int = NULL_SURROGATE
    @JvmField
    protected var consumer: Continuation<Int>? = null

    suspend fun send(element: Int) {
        require(element != NULL_SURROGATE)
        if (offer(element)) {
            return
        }

        return suspendSend(element)
    }

    private fun offer(element: Int): Boolean {
        if (consumer == null) {
            return false
        }

        consumer!!.resume(element)
        consumer = null
        return true
    }

    suspend fun receive(): Int {
        // Cached value
        if (enqueuedValue != NULL_SURROGATE) {
            val result = enqueuedValue
            enqueuedValue = NULL_SURROGATE
            producer!!.resume(Unit)
            return result
        }

        return suspendReceive()
    }

    abstract suspend fun suspendReceive(): Int
    abstract suspend fun suspendSend(element: Int)
}

class NonCancellableChannel : SimpleChannel() {
    override suspend fun suspendReceive(): Int = suspendCoroutineUninterceptedOrReturn {
        consumer = it.intercepted()
        COROUTINE_SUSPENDED
    }

    override suspend fun suspendSend(element: Int) = suspendCoroutineUninterceptedOrReturn<Unit> {
        enqueuedValue = element
        producer = it.intercepted()
        COROUTINE_SUSPENDED
    }
}

class CancellableChannel : SimpleChannel() {
    override suspend fun suspendReceive(): Int = suspendAtomicCancellableCoroutine {
        consumer = it.intercepted()
        COROUTINE_SUSPENDED
    }

    override suspend fun suspendSend(element: Int) = suspendAtomicCancellableCoroutine<Unit> {
        enqueuedValue = element
        producer = it.intercepted()
        COROUTINE_SUSPENDED
    }
}

class CancellableReusableChannel : SimpleChannel() {
    @Suppress("INVISIBLE_MEMBER")
    override suspend fun suspendReceive(): Int = suspendAtomicCancellableCoroutineReusable {
        consumer = it.intercepted()
        COROUTINE_SUSPENDED
    }

    @Suppress("INVISIBLE_MEMBER")
    override suspend fun suspendSend(element: Int) = suspendAtomicCancellableCoroutineReusable<Unit> {
        enqueuedValue = element
        producer = it.intercepted()
        COROUTINE_SUSPENDED
    }
}