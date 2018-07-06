/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.*
import kotlin.test.*

class AsyncTest : TestBase() {
    @Test
    fun testSimple() = runTest {
        expect(1)
        val d = async(coroutineContext) {
            expect(3)
            42
        }
        expect(2)
        assertTrue(d.isActive)
        assertTrue(d.await() == 42)
        assertTrue(!d.isActive)
        expect(4)
        assertTrue(d.await() == 42) // second await -- same result
        finish(5)
    }

    @Test
    fun testUndispatched() = runTest {
        expect(1)
        val d = async(coroutineContext, start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            42
        }
        expect(3)
        assertTrue(!d.isActive)
        assertTrue(d.await() == 42)
        finish(4)
    }

    @Test
    fun testSimpleException() = runTest(
        expected = { it is TestException }
    ) {
        expect(1)
        val d = async(coroutineContext) {
            finish(3)
            throw TestException()
        }
        expect(2)
        d.await() // will throw IOException
    }

    @Test
    fun testDeferAndYieldException() = runTest(
        expected = { it is TestException }
    ) {
        expect(1)
        val d = async(coroutineContext) {
            expect(3)
            yield() // no effect, parent waiting
            finish(4)
            throw TestException()
        }
        expect(2)
        d.await() // will throw IOException
    }

    @Test
    fun testDeferWithTwoWaiters() = runTest {
        expect(1)
        val d = async(coroutineContext) {
            expect(5)
            yield()
            expect(9)
            42
        }
        expect(2)
        launch(coroutineContext) {
            expect(6)
            assertTrue(d.await() == 42)
            expect(11)
        }
        expect(3)
        launch(coroutineContext) {
            expect(7)
            assertTrue(d.await() == 42)
            expect(12)
        }
        expect(4)
        yield() // this actually yields control to async, which produces results and resumes both waiters (in order)
        expect(8)
        yield() // yield again to "d", which completes
        expect(10)
        yield() // yield to both waiters
        finish(13)
    }

    class BadClass {
        override fun equals(other: Any?): Boolean = error("equals")
        override fun hashCode(): Int = error("hashCode")
        override fun toString(): String = error("toString")
    }

    @Test
    fun testDeferBadClass() = runTest {
        val bad = BadClass()
        val d = async(coroutineContext) {
            expect(1)
            bad
        }
        assertTrue(d.await() === bad)
        finish(2)
    }

    private class TestException : Exception()
}