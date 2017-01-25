package kotlinx.coroutines.experimental

import org.junit.Test
import java.io.IOException

class CoroutinesTest : TestBase() {
    @Test
    fun testSimple() = runBlocking {
        expect(1)
        finish(2)
    }

    @Test
    fun testYield() = runBlocking {
        expect(1)
        yield() // effectively does nothing, as we don't have other coroutines
        finish(2)
    }

    @Test
    fun testLaunchAndYieldJoin() = runBlocking {
        expect(1)
        val job = launch(context) {
            expect(2)
            yield()
            expect(4)
        }
        expect(3)
        job.join()
        finish(5)
    }

    @Test
    fun testNested() = runBlocking {
        expect(1)
        launch(context) {
            expect(2)
            launch(context) {
                expect(3)
            }
            expect(4)
        }
        finish(5)
    }

    @Test
    fun testNestedAndYieldJoin() = runBlocking {
        expect(1)
        val j1 = launch(context) {
            expect(2)
            val j2 = launch(context) {
                expect(3)
                yield()
                expect(6)
            }
            expect(4)
            j2.join()
            expect(7)
        }
        expect(5)
        j1.join()
        finish(8)
    }

    @Test
    fun testCancelChildImplicit() = runBlocking {
        expect(1)
        launch(context) {
            expect(2)
            yield() // parent finishes earlier, does not wait for us
            expectUnreached()
        }
        finish(3)
    }

    @Test
    fun testCancelChildExplicit() = runBlocking {
        expect(1)
        val job = launch(context) {
            expect(2)
            yield()
            expectUnreached()
        }
        expect(3)
        job.cancel()
        finish(4)
    }

    @Test
    fun testCancelNestedImplicit() = runBlocking {
        expect(1)
        val j1 = launch(context) {
            expect(2)
            val j2 = launch(context) {
                expect(3)
                yield() // parent finishes earlier, does not wait for us
                expectUnreached()
            }
            expect(4)
        }
        finish(5)
    }

    @Test
    fun testCancelNestedImplicit2() = runBlocking {
        expect(1)
        val j1 = launch(context) {
            expect(2)
            val j2 = launch(context) {
                expect(3)
                yield() // parent finishes earlier, does not wait for us
                expectUnreached()
            }
            expect(4)
            yield() // does not go further, because already cancelled
            expectUnreached()
        }
        finish(5)
    }

    @Test(expected = IOException::class)
    fun testExceptionPropagation(): Unit = runBlocking {
        finish(1)
        throw IOException()
    }

    @Test(expected = CancellationException::class)
    fun testCancelParentOnChildException(): Unit = runBlocking {
        expect(1)
        launch(context) {
            expect(2)
            throw IOException() // does not propagate exception to launch, but cancels parent (!)
        }
        finish(3)
    }

    @Test(expected = CancellationException::class)
    fun testCancelParentOnChildException2(): Unit = runBlocking {
        expect(1)
        launch(context) {
            expect(2)
            throw IOException()
        }
        finish(3)
        yield() // parent is already cancelled (so gets CancellationException on this suspend attempt)
        expectUnreached()
    }

    @Test(expected = CancellationException::class)
    fun testCancelParentOnNestedException(): Unit = runBlocking {
        expect(1)
        launch(context) {
            expect(2)
            launch(context) {
                expect(3)
                throw IOException() // unhandled exception kills all parents
            }
            expect(4)
        }
        finish(5)
    }
}
