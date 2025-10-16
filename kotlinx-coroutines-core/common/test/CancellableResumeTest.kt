package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.test.*

/**
 * Test for [CancellableContinuation.resume] with `onCancellation` parameter.
 */
class CancellableResumeTest : TestBase() {
    @Test
    fun testResumeImmediateNormally() = runTest {
        expect(1)
        val ok = suspendCancellableCoroutine { cont ->
            expect(2)
            cont.invokeOnCancellation { expectUnreached() }
            cont.resume("OK") { _, _, _ -> expectUnreached() }
            expect(3)
        }
        assertEquals("OK", ok)
        finish(4)
    }

    @Test
    fun testResumeImmediateAfterCancel() = runTest(
        expected = { it is TestException }
    ) {
        expect(1)
        suspendCancellableCoroutine { cont ->
            expect(2)
            cont.invokeOnCancellation { expect(3) }
            cont.cancel(TestException("FAIL"))
            expect(4)
            val value = "OK"
            cont.resume(value) { cause, valueToClose, context ->
                expect(5)
                assertSame(value, valueToClose)
                assertSame(context, cont.context)
                assertIs<TestException>(cause)
            }
            finish(6)
        }
        expectUnreached()
    }

    @Test
    fun testResumeImmediateAfterCancelWithHandlerFailure() = runTest(
        expected = { it is TestException },
        unhandled = listOf(
            { it is CompletionHandlerException && it.cause is TestException2 },
            { it is CompletionHandlerException && it.cause is TestException3 }
        )
    ) {
        expect(1)
        suspendCancellableCoroutine { cont ->
            expect(2)
            cont.invokeOnCancellation {
                expect(3)
                throw TestException2("FAIL") // invokeOnCancellation handler fails with exception
            }
            cont.cancel(TestException("FAIL"))
            expect(4)
            val value = "OK"
            cont.resume(value) { cause, valueToClose, context ->
                expect(5)
                assertSame(value, valueToClose)
                assertSame(context, cont.context)
                assertIs<TestException>(cause)
                throw TestException3("FAIL") // onCancellation block fails with exception
            }
            finish(6)
        }
        expectUnreached()
    }

    @Test
    fun testResumeImmediateAfterIndirectCancel() = runTest(
        expected = { it is CancellationException }
    ) {
        expect(1)
        val ctx = coroutineContext
        suspendCancellableCoroutine { cont ->
            expect(2)
            cont.invokeOnCancellation { expect(3) }
            ctx.cancel()
            expect(4)
            val value = "OK"
            cont.resume(value) { cause, valueToClose, context ->
                expect(5)
                assertSame(value, valueToClose)
                assertSame(context, cont.context)
                assertIs<CancellationException>(cause)
            }
            finish(6)
        }
        expectUnreached()
    }

    @Test
    fun testResumeImmediateAfterIndirectCancelWithHandlerFailure() = runTest(
        expected = { it is CancellationException },
        unhandled = listOf(
            { it is CompletionHandlerException && it.cause is TestException2 },
            { it is CompletionHandlerException && it.cause is TestException3 }
        )
    ) {
        expect(1)
        val ctx = coroutineContext
        suspendCancellableCoroutine { cont ->
            expect(2)
            cont.invokeOnCancellation {
                expect(3)
                throw TestException2("FAIL") // invokeOnCancellation handler fails with exception
            }
            ctx.cancel()
            expect(4)
            val value = "OK"
            cont.resume(value) { cause, valueToClose, context ->
                expect(5)
                assertSame(value, valueToClose)
                assertSame(context, cont.context)
                assertIs<CancellationException>(cause)
                throw TestException3("FAIL") // onCancellation block fails with exception
            }
            finish(6)
        }
        expectUnreached()
    }

    @Test
    fun testResumeLaterNormally() = runTest {
        expect(1)
        lateinit var cc: CancellableContinuation<String>
        launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            val ok = suspendCancellableCoroutine { cont ->
                expect(3)
                cont.invokeOnCancellation { expectUnreached() }
                cc = cont
            }
            assertEquals("OK", ok)
            finish(6)
        }
        expect(4)
        cc.resume("OK") { _, _, _ -> expectUnreached() }
        expect(5)
    }

    @Test
    fun testResumeLaterAfterCancel() = runTest {
        expect(1)
        lateinit var cc: CancellableContinuation<String>
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                suspendCancellableCoroutine { cont ->
                    expect(3)
                    cont.invokeOnCancellation { expect(5) }
                    cc = cont
                }
                expectUnreached()
            } catch (_: CancellationException) {
                finish(9)
            }
        }
        expect(4)
        job.cancel(TestCancellationException())
        expect(6)
        val value = "OK"
        cc.resume(value) { cause, valueToClose, context ->
            expect(7)
            assertSame(value, valueToClose)
            assertSame(context, cc.context)
            assertIs<TestCancellationException>(cause)
        }
        expect(8)
    }

    @Test
    fun testResumeLaterAfterCancelWithHandlerFailure() = runTest(
        unhandled = listOf(
            { it is CompletionHandlerException && it.cause is TestException2 },
            { it is CompletionHandlerException && it.cause is TestException3 }
        )
    ) {
        expect(1)
        lateinit var cc: CancellableContinuation<String>
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                suspendCancellableCoroutine { cont ->
                    expect(3)
                    cont.invokeOnCancellation {
                        expect(5)
                        throw TestException2("FAIL") // invokeOnCancellation handler fails with exception
                    }
                    cc = cont
                }
                expectUnreached()
            } catch (_: CancellationException) {
                finish(9)
            }
        }
        expect(4)
        job.cancel(TestCancellationException())
        expect(6)
        val value = "OK"
        cc.resume(value) { cause, valueToClose, context ->
            expect(7)
            assertSame(value, valueToClose)
            assertSame(context, cc.context)
            assertIs<TestCancellationException>(cause)
            throw TestException3("FAIL") // onCancellation block fails with exception
        }
        expect(8)
    }

    @Test
    fun testResumeCancelWhileDispatched() = runTest {
        expect(1)
        lateinit var cc: CancellableContinuation<String>
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                suspendCancellableCoroutine { cont ->
                    expect(3)
                    // resumed first, dispatched, then cancelled, but still got invokeOnCancellation call
                    cont.invokeOnCancellation { cause ->
                        // Note: invokeOnCancellation is called before cc.resume(value) { ... } handler
                        expect(7)
                        assertIs<TestCancellationException>(cause)
                    }
                    cc = cont
                }
                expectUnreached()
            } catch (_: CancellationException) {
                expect(9)
            }
        }
        expect(4)
        val value = "OK"
        cc.resume("OK") { cause, valueToClose, context ->
            // Note: this handler is called after invokeOnCancellation handler
            expect(8)
            assertSame(value, valueToClose)
            assertSame(context, cc.context)
            assertIs<TestCancellationException>(cause)
        }
        expect(5)
        job.cancel(TestCancellationException()) // cancel while execution is dispatched
        expect(6)
        yield() // to coroutine -- throws cancellation exception
        finish(10)
    }

    @Test
    fun testResumeCancelWhileDispatchedWithHandlerFailure() = runTest(
        unhandled = listOf(
            { it is CompletionHandlerException && it.cause is TestException2 },
            { it is CompletionHandlerException && it.cause is TestException3 }
        )
    ) {
        expect(1)
        lateinit var cc: CancellableContinuation<String>
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                suspendCancellableCoroutine { cont ->
                    expect(3)
                    // resumed first, dispatched, then cancelled, but still got invokeOnCancellation call
                    cont.invokeOnCancellation { cause ->
                        // Note: invokeOnCancellation is called before cc.resume(value) { ... } handler
                        expect(7)
                        assertIs<TestCancellationException>(cause)
                        throw TestException2("FAIL") // invokeOnCancellation handler fails with exception
                    }
                    cc = cont
                }
                expectUnreached()
            } catch (_: CancellationException) {
                expect(9)
            }
        }
        expect(4)
        val value = "OK"
        cc.resume(value) { cause, valueToClose, context ->
            // Note: this handler is called after invokeOnCancellation handler
            expect(8)
            assertSame(value, valueToClose)
            assertSame(context, cc.context)
            assertIs<TestCancellationException>(cause)
            throw TestException3("FAIL") // onCancellation block fails with exception
        }
        expect(5)
        job.cancel(TestCancellationException()) // cancel while execution is dispatched
        expect(6)
        yield() // to coroutine -- throws cancellation exception
        finish(10)
    }

    @Test
    fun testResumeUnconfined() = runTest {
        val outerScope = this
        withContext(Dispatchers.Unconfined) {
            val result = suspendCancellableCoroutine {
                outerScope.launch {
                    it.resume("OK") { _, _, _ ->
                        expectUnreached()
                    }
                }
            }
            assertEquals("OK", result)
        }
    }
}
