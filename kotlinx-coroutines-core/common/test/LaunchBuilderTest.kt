/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines

import kotlin.test.*

class LaunchBuilderTest : TestBase() {
    @Test
    fun testDefaultNoHandlers() = runTest {
        expect(1)
        val b0 = launchBuilder {
            expect(4)
        }
        expect(2)
        val job = b0.build()
        expect(3)
        assertRunning(job)
        yield()
        assertCompleted(job)
        finish(5)
    }

    @Test
    fun testUndispatchedNoHandlers() = runTest {
        expect(1)
        val b0 = launchBuilder(start = CoroutineStart.UNDISPATCHED) {
            expect(3)
        }
        expect(2)
        val job = b0.build()
        assertCompleted(job)
        finish(4)
    }

    @Test
    fun testCatchNoException() =
        testCatch<TestException>(expectCaught = false, expectCancelled = false) {  }

    @Test
    fun testCatchWrongException() =
        testCatch<TestException2>(expectCaught = false, expectCancelled = true) { throw TestException() }

    @Test
    fun testCatchTestException() =
        testCatch<TestException>(expectCaught = true, expectCancelled = false) { throw TestException() }

    @Test
    fun testCatchThrowable() =
        testCatch<Throwable>(expectCaught = true, expectCancelled = false) { throw TestException() }

    private inline fun <reified CatchE : Throwable> testCatch(
        expectCaught: Boolean,
        expectCancelled: Boolean,
        crossinline throwBlock: () -> Unit
    ) = runTest(
        expected = { it: Throwable -> it is TestException }.takeIf { expectCancelled }
    ) {
        expect(1)
        val b0 = launchBuilder(start = CoroutineStart.UNDISPATCHED) {
            expect(4)
            throwBlock()
        }
        expect(2)
        val b1 = b0.catch<CatchE> { e ->
            if (expectCaught) {
                expect(5)
            } else {
                expectUnreached()
            }
        }
        expect(3)
        val job = b1.build()
        if (expectCancelled) {
            assertCancelled(job)
        } else {
            assertCompleted(job)
        }
        finish(if (expectCaught) 6 else 5)
    }

    @Test
    fun testCatchOneThrowAnother() = runTest(
        expected = { it is TestException2 }
    ) {
        expect(1)
        launchBuilder {
            expect(2)
            throw TestException("OK")
        }.catch<TestException> { e ->
            finish(3)
            assertEquals("OK", e.message)
            throw TestException2()
        }.build()
    }

    @Test
    fun testCatchTwoFirstCatches() = runTest {
        expect(1)
        launchBuilder {
            throw TestException1()
        }.catch<TestException1> { e ->
            finish(2)
            assertEquals(TestException1::class, e::class)
        }.catch<TestException2> { e ->
            expectUnreached()
        }.build()
    }

    @Test
    fun testCatchTwoSecondCatches() = runTest {
        expect(1)
        launchBuilder {
            throw TestException2()
        }.catch<TestException1> { e ->
            expectUnreached()
        }.catch<TestException2> { e ->
            finish(2)
            assertEquals(TestException2::class, e::class)
        }.build()
    }

    @Test
    fun testCatchTwoNoneCatches() = runTest(
        expected = { it is TestException3 }
    ) {
        expect(1)
        launchBuilder {
            finish(2)
            throw TestException3()
        }.catch<TestException1> { e ->
            expectUnreached()
        }.catch<TestException2> { e ->
            expectUnreached()
        }.build()
    }

    @Test
    fun testFinallyNoException() = runTest {
        expect(1)
        launchBuilder {
            expect(2)
        }.finally { e ->
            finish(3)
            assertNull(e)
        }.build()
    }

    @Test
    fun testFinallyWithException() = runTest(
        expected = { it is TestException }
    ) {
        expect(1)
        launchBuilder {
            expect(2)
            throw TestException("OK")
        }.finally { e ->
            finish(3)
            assertTrue(e is TestException)
            assertEquals("OK", e.message)
        }.build()
    }

    @Test
    fun testFinallyCaughtException() = runTest {
        expect(1)
        launchBuilder {
            expect(2)
            throw TestException("OK")
        }.catch<TestException> { e ->
            expect(3)
            assertSame(TestException::class, e::class)
            assertEquals("OK", e.message)
        }.finally { e ->
            finish(4)
            assertNull(e)
        }.build()
    }

    private fun assertRunning(job: Job) {
        assertTrue(job.isActive)
        assertFalse(job.isCompleted)
        assertFalse(job.isCancelled)
    }

    private fun assertCompleted(job: Job) {
        assertFalse(job.isActive)
        assertTrue(job.isCompleted)
        assertFalse(job.isCancelled)
    }

    private fun assertCancelled(job: Job) {
        assertFalse(job.isActive)
        assertTrue(job.isCompleted)
        assertTrue(job.isCancelled)
    }
}