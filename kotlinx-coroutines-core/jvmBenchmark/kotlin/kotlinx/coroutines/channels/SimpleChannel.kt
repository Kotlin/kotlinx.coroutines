package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

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
    override suspend fun suspendReceive(): Int = suspendCancellableCoroutine {
        consumer = it.intercepted()
        COROUTINE_SUSPENDED
    }

    override suspend fun suspendSend(element: Int) = suspendCancellableCoroutine<Unit> {
        enqueuedValue = element
        producer = it.intercepted()
        COROUTINE_SUSPENDED
    }
}

class CancellableReusableChannel : SimpleChannel() {
    override suspend fun suspendReceive(): Int = suspendCancellableCoroutineReusable {
        consumer = it.intercepted()
        COROUTINE_SUSPENDED
    }

    override suspend fun suspendSend(element: Int) = suspendCancellableCoroutineReusable<Unit> {
        enqueuedValue = element
        producer = it.intercepted()
        COROUTINE_SUSPENDED
    }
}
