package kotlinx.coroutines.experimental

import org.junit.Test
import java.io.IOException

class DeferTest : TestBase() {
    @Test
    fun testSimple(): Unit = runBlocking {
        expect(1)
        val d = defer(context) {
            expect(3)
            42
        }
        expect(2)
        check(d.isActive)
        check(d.await() == 42)
        check(!d.isActive)
        expect(4)
        check(d.await() == 42) // second await -- same result
        finish(5)
    }

    @Test(expected = IOException::class)
    fun testSimpleException(): Unit = runBlocking {
        expect(1)
        val d = defer(context) {
            finish(3)
            throw IOException()
        }
        expect(2)
        d.await() // will throw IOException
    }

    @Test(expected = IOException::class)
    fun testDeferAndYieldException(): Unit = runBlocking {
        expect(1)
        val d = defer(context) {
            expect(3)
            yield() // no effect, parent waiting
            finish(4)
            throw IOException()
        }
        expect(2)
        d.await() // will throw IOException
    }

    @Test
    fun testDeferWithTwoWaiters() = runBlocking {
        expect(1)
        val d = defer(context) {
            expect(5)
            yield()
            expect(9)
            42
        }
        expect(2)
        launch(context) {
            expect(6)
            check(d.await() == 42)
            expect(11)
        }
        expect(3)
        launch(context) {
            expect(7)
            check(d.await() == 42)
            expect(12)
        }
        expect(4)
        yield() // this actually yields control to defer, which produces results and resumes both waiters (in order)
        expect(8)
        yield() // yield again to "d", which completes
        expect(10)
        yield() // yield to both waiters
        finish(13)
    }
}