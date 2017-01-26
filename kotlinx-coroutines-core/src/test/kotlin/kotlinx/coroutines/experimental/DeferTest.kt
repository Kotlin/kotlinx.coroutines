package kotlinx.coroutines.experimental

import org.junit.Test
import java.io.IOException

class DeferTest : TestBase() {
    @Test
    fun testSimple(): Unit = runBlocking {
        expect(1)
        val d = defer(context) {
            expect(2)
            42
        }
        expect(3)
        check(!d.isActive)
        check(d.await() == 42)
        expect(4)
        check(d.await() == 42) // second await -- same result
        finish(5)
    }

    @Test
    fun testDeferAndYield(): Unit = runBlocking {
        expect(1)
        val d = defer(context) {
            expect(2)
            yield()
            expect(4)
            42
        }
        expect(3)
        check(d.isActive)
        check(d.await() == 42)
        check(!d.isActive)
        expect(5)
        check(d.await() == 42) // second await -- same result
        finish(6)
    }

    @Test(expected = IOException::class)
    fun testSimpleException(): Unit = runBlocking {
        expect(1)
        val d = defer(context) {
            expect(2)
            throw IOException()
        }
        finish(3)
        d.await() // will throw IOException
    }

    @Test(expected = IOException::class)
    fun testDeferAndYieldException(): Unit = runBlocking {
        expect(1)
        val d = defer(context) {
            expect(2)
            yield()
            finish(4)
            throw IOException()
        }
        expect(3)
        d.await() // will throw IOException
    }

    @Test
    fun testDeferWithTwoWaiters() = runBlocking {
        expect(1)
        val d = defer(context) {
            expect(2)
            yield()
            expect(8)
            42
        }
        expect(3)
        launch(context) {
            expect(4)
            check(d.await() == 42)
            expect(9)
        }
        expect(5)
        launch(context) {
            expect(6)
            check(d.await() == 42)
            expect(10)
        }
        expect(7)
        yield() // this actually yields control to defer, which produces results and resumes both waiters (in order)
        finish(11)
    }
}