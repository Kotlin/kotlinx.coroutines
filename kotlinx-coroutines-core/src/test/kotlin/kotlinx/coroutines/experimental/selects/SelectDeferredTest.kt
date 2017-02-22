package kotlinx.coroutines.experimental.selects

import kotlinx.coroutines.experimental.*
import org.junit.Assert.assertEquals
import org.junit.Test

class SelectDeferredTest : TestBase() {
    @Test
    fun testSimpleReturnsImmediately() = runBlocking<Unit> {
        expect(1)
        val d1 = async<Int>(context) {
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
    fun testSimpleWithYield() = runBlocking<Unit> {
        expect(1)
        val d1 = async<Int>(context) {
            expect(3)
            42
        }
        launch(context) {
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
    fun testSelectIncompleteLazy() = runBlocking<Unit> {
        expect(1)
        val d1 = async<Int>(context, start = false) {
            expect(5)
            42
        }
        launch(context) {
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
    fun testSelectTwo() = runBlocking<Unit> {
        expect(1)
        val d1 = async<String>(context) {
            expect(3)
            yield() // to the other deffered
            expect(5)
            yield() // to fired select
            expect(7)
            "d1"
        }
        val d2 = async<String>(context) {
            expect(4)
            "d2" // returns result
        }
        expect(2)
        val res = select<String> {
            d1.onAwait { v1 ->
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

}