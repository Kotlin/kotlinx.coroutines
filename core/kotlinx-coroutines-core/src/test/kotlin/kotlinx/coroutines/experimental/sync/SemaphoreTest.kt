package kotlinx.coroutines.experimental.sync

import kotlin.coroutines.experimental.*
import kotlinx.coroutines.experimental.TestBase
import kotlinx.coroutines.experimental.launch
import kotlinx.coroutines.experimental.yield
import kotlin.test.Test

class SemaphoreTest : TestBase() {

    @Test
    fun testUseAllPermits() = runTest {
        val sema = Semaphore(2)

        launch(coroutineContext) {
            expect(3)
            sema.release()
            expect(4)
        }

        expect(1)
        sema.acquire()
        sema.acquire()
        expect(2)

        sema.acquire() // suspend

        finish(5)
    }

    @Test
    fun testNeedPermits() = runTest {
        val sema = Semaphore(-1)

        launch(coroutineContext) {
            expect(2)
            sema.release()
            sema.release()
            expect(3)
        }

        expect(1)

        sema.acquire() // suspend

        finish(4)
    }

    @Test
    fun testFairness() = runTest {
        val sema = Semaphore(0)

        launch(coroutineContext) {
            // first to acquire
            expect(2)

            sema.acquire() // suspend

            expect(6)
        }

        launch(coroutineContext) {
            // second to acquire
            expect(3)

            sema.acquire() // suspend

            expect(9)
        }

        expect(1)

        yield()

        expect(4)
        sema.release()
        expect(5)

        yield()

        expect(7)
        sema.release()
        expect(8)

        yield()

        finish(10)
    }
}
