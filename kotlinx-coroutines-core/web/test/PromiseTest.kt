package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.js.*
import kotlin.test.*

@OptIn(ExperimentalWasmJsInterop::class)
class PromiseTestWeb : TestBase() {
    @Test
    fun testPromiseResolvedAsDeferred() = GlobalScope.promise {
        val promise = Promise { resolve, _ ->
            resolve("OK".toJsReference())
        }
        val deferred = promise.asDeferred()
        assertEquals("OK", deferred.await().get())
        null
    }

    @Test
    fun testPromiseRejectedAsDeferred() = GlobalScope.promise {
        lateinit var promiseReject: (JsPromiseError) -> Unit
        val promise = Promise<JsAny?> { _, reject ->
            promiseReject = reject
        }
        val deferred = promise.asDeferred()
        // reject after converting to deferred to avoid "Unhandled promise rejection" warnings
        @Suppress("CAST_NEVER_SUCCEEDS")
        promiseReject(TestException("Rejected").toJsReference() as JsPromiseError)
        try {
            deferred.await()
            expectUnreached()
        } catch (e: Throwable) {
            assertIs<TestException>(e)
            assertEquals("Rejected", e.message)
        }
        null
    }

    @Test
    fun testCompletedDeferredAsPromise() = GlobalScope.promise {
        val deferred = async(start = CoroutineStart.UNDISPATCHED) {
            // completed right away
            "OK".toJsReference()
        }
        val promise = deferred.asPromise()
        assertEquals("OK", promise.await().get())
        null
    }

    @Test
    fun testWaitForDeferredAsPromise() = GlobalScope.promise {
        val deferred = async {
            // will complete later
            "OK".toJsReference()
        }
        val promise = deferred.asPromise()
        assertEquals("OK", promise.await().get()) // await yields main thread to deferred coroutine
        null
    }

    @Test
    fun testCancellableAwaitPromise() = GlobalScope.promise {
        lateinit var r: (JsAny) -> Unit
        val toAwait = Promise<JsAny?> { resolve, _ -> r = resolve }
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            toAwait.await() // suspends
        }
        job.cancel() // cancel the job
        r("fail".toJsString()) // too late, the waiting job was already cancelled
        null
    }

    @Test
    fun testAsPromiseAsDeferred() = GlobalScope.promise {
        val deferred = async { "OK".toJsString() }
        val promise = deferred.asPromise()
        val d2 = promise.asDeferred<JsString>()
        assertSame(d2, deferred)
        assertEquals("OK", d2.await().toString())
        null
    }

    @Test
    fun testAwaitPromiseRejectedWithNonKotlinException() = GlobalScope.promise {
        val toAwait = jsPromiseRejectedWithString()
        val throwable = async(start = CoroutineStart.UNDISPATCHED) {
            assertFails { toAwait.await() }
        }
        val throwableResolved = throwable.await()
        assertEquals(true, throwableResolved.message?.contains("Rejected"), "${throwableResolved.message}")
        null
    }

    @Test
    fun testAwaitPromiseRejectedWithKotlinException() = GlobalScope.promise {
        lateinit var r: (JsPromiseError) -> Unit
        val toAwait = Promise<JsAny?> { _, reject -> r = reject }
        val throwable = async(start = CoroutineStart.UNDISPATCHED) {
            assertFails { toAwait.await<JsAny?>() }
        }
        @Suppress("CAST_NEVER_SUCCEEDS")
        r(RuntimeException("Rejected").toJsReference() as JsPromiseError)
        assertIs<Exception>(throwable.await())
        assertEquals("Rejected", throwable.await().message)
        null
    }
}

@OptIn(ExperimentalWasmJsInterop::class)
private fun jsPromiseRejectedWithString(): Promise<JsBigInt> = js("Promise.reject(\"Rejected\")")