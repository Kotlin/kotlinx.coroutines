@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines.selects

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

class SelectDeferredTest : TestBase() {
    @Test
    fun testSimpleReturnsImmediately() = runTest {
        expect(1)
        val d1 = async {
            expect(3)
            42
        }
        expect(2)
        val res = select<String> {
            d1.onAwait { v ->
                expect(4)
                assertEquals(42, v)
                "OK"
            }
        }
        expect(5)
        assertEquals("OK", res)
        finish(6)
    }

    @Test
    fun testSimpleWithYield() = runTest {
        expect(1)
        val d1 = async {
            expect(3)
            42
        }
        launch {
            expect(4)
            yield() // back to main
            expect(6)
        }
        expect(2)
        val res = select<String> {
            d1.onAwait { v ->
                expect(5)
                assertEquals(42, v)
                yield() // to launch
                expect(7)
                "OK"
            }
        }
        finish(8)
        assertEquals("OK", res)
    }

    @Test
    fun testSelectIncompleteLazy() = runTest {
        expect(1)
        val d1 = async(start = CoroutineStart.LAZY) {
            expect(5)
            42
        }
        launch {
            expect(3)
            val res = select<String> {
                d1.onAwait { v ->
                    expect(7)
                    assertEquals(42, v)
                    "OK"
                }
            }
            expect(8)
            assertEquals("OK", res)
        }
        expect(2)
        yield() // to launch
        expect(4)
        yield() // to started async
        expect(6)
        yield() // to triggered select
        finish(9)
    }

    @Test
    fun testSelectTwo() = runTest {
        expect(1)
        val d1 = async {
            expect(3)
            yield() // to the other deffered
            expect(5)
            yield() // to fired select
            expect(7)
            "d1"
        }
        val d2 = async {
            expect(4)
            "d2" // returns result
        }
        expect(2)
        val res = select<String> {
            d1.onAwait {
                expectUnreached()
                "FAIL"
            }
            d2.onAwait { v2 ->
                expect(6)
                assertEquals("d2", v2)
                yield() // to first deferred
                expect(8)
                "OK"
            }
        }
        assertEquals("OK", res)
        finish(9)
    }

    /**
     * Tests that completing a [Deferred] with an exception will cause the [select] that uses [Deferred.onAwait]
     * to throw the same exception.
     */
    @Test
    fun testSelectFailure() = runTest {
        val d = CompletableDeferred<Nothing>()
        d.completeExceptionally(TestException())
        val d2 = CompletableDeferred(42)
        assertFailsWith<TestException> {
            select {
                d.onAwait { expectUnreached() }
                d2.onAwait { 4 }
            }
        }
    }

    @Test
    fun testSelectCancel() = runTest(
        expected = { it is CancellationException }
    ) {
        expect(1)
        val d = CompletableDeferred<String>()
        launch {
            finish(3)
            d.cancel() // will cancel after select starts
        }
        expect(2)
        select<Unit> {
            d.onAwait {
                expectUnreached() // will not select
            }
        }
        expectUnreached()
    }

    @Test
    fun testSelectIncomplete() = runTest {
        val deferred = async { Wrapper("OK") }
        val result = select<Wrapper> {
            assertFalse(deferred.isCompleted)
            assertTrue(deferred.isActive)
            deferred.onAwait {
                it
            }
        }

        assertEquals("OK", result.value)
    }

    @Test
    fun testSelectIncompleteFastPath() = runTest {
        val deferred = async(Dispatchers.Unconfined) { Wrapper("OK") }
        val result = select<Wrapper> {
            assertTrue(deferred.isCompleted)
            assertFalse(deferred.isActive)
            deferred.onAwait {
                it
            }
        }

        assertEquals("OK", result.value)
    }

    private class Wrapper(val value: String) : Incomplete {
        override val isActive: Boolean
            get() = error("")
        override val list: NodeList?
            get() = error("")
    }
}
