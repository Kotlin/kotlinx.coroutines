/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines

import kotlin.test.*

/**
 * Test for [CancellableContinuation.resume] with `onCancellation` parameter.
 */
class CancellableResumeTest : TestBase() {
    @Test
    fun testResumeImmediateNormally() = runTest {
        expect(1)
        val ok = suspendCancellableCoroutine<String> { cont ->
            expect(2)
            cont.invokeOnCancellation { expectUnreached() }
            cont.resume("OK") { expectUnreached() }
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
        suspendCancellableCoroutine<String> { cont ->
            expect(2)
            cont.invokeOnCancellation { expect(3) }
            cont.cancel(TestException("FAIL"))
            expect(4)
            cont.resume("OK") { cause ->
                expect(5)
                assertTrue(cause is TestException)
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
        suspendCancellableCoroutine<String> { cont ->
            expect(2)
            cont.invokeOnCancellation { expect(3) }
            ctx.cancel()
            expect(4)
            cont.resume("OK") { cause ->
                expect(5)
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
            val ok = suspendCancellableCoroutine<String> { cont ->
                expect(3)
                cont.invokeOnCancellation { expectUnreached() }
                cc = cont
            }
            assertEquals("OK", ok)
            finish(6)
        }
        expect(4)
        cc.resume("OK") { expectUnreached() }
        expect(5)
    }

    @Test
    fun testResumeLaterAfterCancel() = runTest {
        expect(1)
        lateinit var cc: CancellableContinuation<String>
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                suspendCancellableCoroutine<String> { cont ->
                    expect(3)
                    cont.invokeOnCancellation { expect(5) }
                    cc = cont
                }
                expectUnreached()
            } catch (e: CancellationException) {
                finish(9)
            }
        }
        expect(4)
        job.cancel(TestCancellationException())
        expect(6)
        cc.resume("OK") { cause ->
            expect(7)
            assertTrue(cause is TestCancellationException)
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
                suspendCancellableCoroutine<String> { cont ->
                    expect(3)
                    // resumed first, then cancelled, so no invokeOnCancellation call
                    cont.invokeOnCancellation { expectUnreached() }
                    cc = cont
                }
                expectUnreached()
            } catch (e: CancellationException) {
                expect(8)
            }
        }
        expect(4)
        cc.resume("OK") { cause ->
            expect(7)
            assertTrue(cause is TestCancellationException)
        }
        expect(5)
        job.cancel(TestCancellationException()) // cancel while execution is dispatched
        expect(6)
        yield() // to coroutine -- throws cancellation exception
        finish(9)
    }


    @Test
    fun testResumeUnconfined() = runTest {
        val outerScope = this
        withContext(Dispatchers.Unconfined) {
            val result = suspendCancellableCoroutine<String> {
                outerScope.launch { it.resume("OK", {}) }
            }
            assertEquals("OK", result)
        }
    }
}