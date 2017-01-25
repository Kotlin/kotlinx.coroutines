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
}