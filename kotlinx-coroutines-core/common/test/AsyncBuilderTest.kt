/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.test.*

class AsyncBuilderTest : TestBase() {
    @Test
    fun testNoHandlers() = runTest {
        expect(1)
        val deferred = asyncBuilder {
            expect(3)
            "OK"
        }.build()
        expect(2)
        assertEquals("OK", deferred.await())
        finish(4)
    }

    @Test
    fun testCatchNoException() = runTest {
        expect(1)
        val deferred = asyncBuilder {
            expect(3)
            "OK"
        }.catch<TestException> {
            error("should not happen")
        }.build()
        expect(2)
        assertEquals("OK", deferred.await())
        finish(4)
    }

    @Test
    fun testCatchWrongException() = runTest {
        expect(1)
        val deferred = asyncBuilder(NonCancellable) {
            expect(3)
            throw TestException()
            @Suppress("UNREACHABLE_CODE")
            "OK"
        }.catch<TestException2> {
            error("should not happen")
        }.build()
        expect(2)
        val result = runCatching { deferred.await() }
        assertTrue(result.isFailure)
        assertTrue(result.exceptionOrNull() is TestException)
        assertTrue(deferred.isCancelled)
        assertTrue(deferred.getCompletionExceptionOrNull() is TestException)
        finish(4)
    }

    @Test
    fun testCatchTestException() = runTest {
        expect(1)
        val deferred = asyncBuilder(NonCancellable) {
            expect(3)
            throw TestException("O")
            @Suppress("UNREACHABLE_CODE")
            "FAIL"
        }.catch<TestException> { e ->
            expect(4)
            assertSame(TestException::class, e::class)
            e.message + "K"
        }.build()
        expect(2)
        assertEquals("OK", deferred.await())
        finish(5)
    }

    @Test
    fun testCatchThrowableException() = runTest {
        expect(1)
        val deferred = asyncBuilder(NonCancellable) {
            expect(3)
            throw TestException("O")
            @Suppress("UNREACHABLE_CODE")
            "FAIL"
        }.catch<Throwable> { e ->
            expect(4)
            assertSame(TestException::class, e::class)
            e.message + "K"
        }.build()
        expect(2)
        assertEquals("OK", deferred.await())
        finish(5)
    }

    @Test
    fun testCatchOneThrowAnother() = runTest {
        expect(1)
        val deferred = asyncBuilder(NonCancellable) {
            expect(3)
            throw TestException1("O")
            @Suppress("UNREACHABLE_CODE")
            "FAIL"
        }.catch<TestException1> { e ->
            expect(4)
            assertSame(TestException1::class, e::class)
            throw TestException2(e.message + "K")
        }.build()
        expect(2)
        val result = runCatching { deferred.await() }
        assertTrue(result.isFailure)
        assertTrue(result.exceptionOrNull() is TestException2)
        assertTrue(deferred.isCancelled)
        assertTrue(deferred.getCompletionExceptionOrNull() is TestException2)
        assertEquals("OK", deferred.getCompletionExceptionOrNull()?.message)
        finish(5)
    }
}