/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlin.js.*
import kotlin.test.*

class PromiseTest : TestBase() {
    @Test
    fun testPromiseResolvedAsDeferred() = GlobalScope.promise {
        val promise = Promise<String> { resolve, _ ->
            resolve("OK")
        }
        val deferred = promise.asDeferred()
        assertEquals("OK", deferred.await())
    }
    
    @Test
    fun testPromiseRejectedAsDeferred() = GlobalScope.promise {
        lateinit var promiseReject: (Throwable) -> Unit
        val promise = Promise<String> { _, reject ->
            promiseReject = reject
        }
        val deferred = promise.asDeferred()
        // reject after converting to deferred to avoid "Unhandled promise rejection" warnings
        promiseReject(TestException("Rejected"))
        try {
            deferred.await()
            expectUnreached()
        } catch (e: Throwable) {
            assertTrue(e is TestException)
            assertEquals("Rejected", e.message)
        }
    }

    @Test
    fun testCompletedDeferredAsPromise() = GlobalScope.promise {
        val deferred = async(start = CoroutineStart.UNDISPATCHED) {
            // completed right away
            "OK"
        }
        val promise = deferred.asPromise()
        assertEquals("OK", promise.await())
    }

    @Test
    fun testWaitForDeferredAsPromise() = GlobalScope.promise {
        val deferred = async {
            // will complete later
            "OK"
        }
        val promise = deferred.asPromise()
        assertEquals("OK", promise.await()) // await yields main thread to deferred coroutine
    }

    @Test
    fun testCancellableAwaitPromise() = GlobalScope.promise {
        lateinit var r: (String) -> Unit
        val toAwait = Promise<String> { resolve, _ -> r = resolve }
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            toAwait.await() // suspends
        }
        job.cancel() // cancel the job
        r("fail") // too late, the waiting job was already cancelled
    }

    @Test
    fun testAsPromiseAsDeferred() = GlobalScope.promise {
        val deferred = async { "OK" }
        val promise = deferred.asPromise()
        val d2 = promise.asDeferred()
        assertTrue(d2 === deferred)
        assertEquals("OK", d2.await())
    }

    private class TestException(message: String) : Exception(message)
}