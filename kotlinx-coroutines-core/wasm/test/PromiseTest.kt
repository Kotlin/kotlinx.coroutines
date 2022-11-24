/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.js.*
import kotlin.test.*

class PromiseTest : TestBase() {
    @Test
    fun testPromiseResolvedAsDeferred() = GlobalScope.promise {
        val promise = Promise<Dynamic?> { resolve, _ ->
            resolve("OK" as Dynamic)
        }
        val deferred = promise.asDeferred<String>()
        assertEquals("OK", deferred.await())
    }

    @Test
    fun testPromiseRejectedAsDeferred() = GlobalScope.promise {
        lateinit var promiseReject: (Dynamic) -> Unit
        val promise = Promise<Dynamic?> { _, reject ->
            promiseReject = reject
        }
        val deferred = promise.asDeferred<String>()
        // reject after converting to deferred to avoid "Unhandled promise rejection" warnings
        promiseReject(TestException("Rejected") as Dynamic)
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
        lateinit var r: (Dynamic) -> Unit
        val toAwait = Promise<Dynamic?> { resolve, _ -> r = resolve }
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            toAwait.await() // suspends
        }
        job.cancel() // cancel the job
        r("fail" as Dynamic) // too late, the waiting job was already cancelled
    }

    @Test
    fun testAsPromiseAsDeferred() = GlobalScope.promise {
        val deferred = async { "OK" }
        val promise = deferred.asPromise()
        val d2 = promise.asDeferred<String>()
        assertSame(d2, deferred)
        assertEquals("OK", d2.await())
    }

    @Test
    fun testLeverageTestResult(): TestResult {
        // Cannot use expect(..) here
        var seq = 0
        val result = runTest {
            ++seq
        }
        return result.then {
            if (seq != 1) error("Unexpected result: $seq")
            null
        }
    }
}
