package kotlinx.coroutines.experimental

import org.junit.Test
import java.io.IOException

class LazyDeferTest : TestBase() {
    @Test
    fun testSimple(): Unit = runBlocking {
        expect(1)
        val d = lazyDefer(context) {
            expect(3)
            42
        }
        expect(2)
        check(d.isActive && !d.isComputing)
        check(d.await() == 42)
        check(!d.isActive && !d.isComputing)
        expect(4)
        check(d.await() == 42) // second await -- same result
        finish(5)
    }

    @Test
    fun testLazyDeferAndYield(): Unit = runBlocking {
        expect(1)
        val d = lazyDefer(context) {
            expect(3)
            yield() // this has not effect, because parent coroutine is waiting
            expect(4)
            42
        }
        expect(2)
        check(d.isActive && !d.isComputing)
        check(d.await() == 42)
        check(!d.isActive && !d.isComputing)
        expect(5)
        check(d.await() == 42) // second await -- same result
        finish(6)
    }

    @Test
    fun testLazyDeferAndYield2(): Unit = runBlocking {
        expect(1)
        val d = lazyDefer(context) {
            expect(7)
            42
        }
        expect(2)
        check(d.isActive && !d.isComputing)
        launch(context) { // see how it looks from another coroutine
            expect(4)
            check(d.isActive && !d.isComputing)
            yield() // yield back to main
            expect(6)
            check(d.isActive && d.isComputing) // started by main!
            yield() // yield to d
        }
        expect(3)
        check(d.isActive && !d.isComputing)
        yield() // yield to second child (lazy defer is not computing yet)
        expect(5)
        check(d.isActive && !d.isComputing)
        check(d.await() == 42) // starts computing
        check(!d.isActive && !d.isComputing)
        finish(8)
    }

    @Test(expected = IOException::class)
    fun testSimpleException(): Unit = runBlocking {
        expect(1)
        val d = lazyDefer(context) {
            finish(3)
            throw IOException()
        }
        expect(2)
        check(d.isActive && !d.isComputing)
        d.await() // will throw IOException
    }

    @Test(expected = IOException::class)
    fun testLazyDeferAndYieldException(): Unit = runBlocking {
        expect(1)
        val d = lazyDefer(context) {
            expect(3)
            yield() // this has not effect, because parent coroutine is waiting
            finish(4)
            throw IOException()
        }
        expect(2)
        check(d.isActive && !d.isComputing)
        d.await() // will throw IOException
    }

    @Test
    fun testCatchException(): Unit = runBlocking {
        expect(1)
        val d = lazyDefer(context) {
            expect(3)
            throw IOException()
        }
        expect(2)
        check(d.isActive && !d.isComputing)
        try {
            d.await() // will throw IOException
        } catch (e: IOException) {
            check(!d.isActive && !d.isComputing)
            expect(4)
        }
        finish(5)
    }

    @Test
    fun testStart(): Unit = runBlocking {
        expect(1)
        val d = lazyDefer(context) {
            expect(4)
            42
        }
        expect(2)
        check(d.isActive && !d.isComputing)
        check(d.start())
        check(d.isActive && d.isComputing)
        expect(3)
        check(!d.start())
        yield() // yield to started coroutine
        check(!d.isActive && !d.isComputing) // and it finishes
        expect(5)
        check(d.await() == 42) // await sees result
        finish(6)
    }

    @Test(expected = CancellationException::class)
    fun testCancelBeforeStart(): Unit = runBlocking {
        expect(1)
        val d = lazyDefer(context) {
            expectUnreached()
            42
        }
        expect(2)
        check(d.isActive && !d.isComputing)
        check(d.cancel())
        check(!d.isActive && !d.isComputing)
        check(!d.cancel())
        check(!d.start())
        finish(3)
        check(d.await() == 42) // await shall throw CancellationException
        expectUnreached()
    }

    @Test(expected = CancellationException::class)
    fun testCancelWhileComputing(): Unit = runBlocking {
        expect(1)
        val d = lazyDefer(context) {
            expect(4)
            yield() // yield to main, that is going to cancel us
            expectUnreached()
            42
        }
        expect(2)
        check(d.isActive && !d.isComputing)
        check(d.start())
        check(d.isActive && d.isComputing)
        expect(3)
        yield() // yield to d
        expect(5)
        check(d.isActive && d.isComputing)
        check(d.cancel())
        check(!d.isActive && !d.isComputing)
        check(!d.cancel())
        finish(6)
        check(d.await() == 42) // await shall throw CancellationException
        expectUnreached()
    }
}