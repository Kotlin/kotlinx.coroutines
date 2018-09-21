/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.channels

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
public class CancellableChannel {
    companion object {
        const val NULL_SURROGATE: Int = -1
    }

    private var producer: Continuation<Unit>? = null
    private var enqueuedValue: Int = NULL_SURROGATE
    private var consumer: Continuation<Int>? = null

    suspend fun send(element: Int) {
        require(element != NULL_SURROGATE)
        if (offer(element)) {
            return
        }

        return suspendCancellableCoroutine {
            enqueuedValue = element
            producer = it.intercepted()
            COROUTINE_SUSPENDED
        }
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

        return suspendCancellableCoroutine {
            consumer = it.intercepted()
            COROUTINE_SUSPENDED
        }
    }
}
