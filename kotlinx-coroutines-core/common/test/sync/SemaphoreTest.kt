package kotlinx.coroutines.sync

import kotlinx.coroutines.TestBase
import kotlinx.coroutines.launch
import kotlinx.coroutines.selects.SelectClause2
import kotlinx.coroutines.yield
import kotlin.test.Test
import kotlin.test.assertFails
import kotlin.test.assertFailsWith

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
            yield() // immediately continue
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

/**
 * Test usage of a 0-1 semaphore as a [Mutex].
 */
class SemaphoreMutexTest : AbstractMutexTest() {
    override fun createMutex(): Mutex {
        val sema = Semaphore(1)
        return object : Mutex {
            override val isLocked: Boolean get() = sema.permits == 0
            override fun tryLock(owner: Any?) = sema.tryAcquire()
            override suspend fun lock(owner: Any?) = sema.acquire()
            override val onLock: SelectClause2<Any?, Mutex>
                get() = TODO("not implemented")

            override fun holdsLock(owner: Any): Boolean {
                TODO("not implemented")
            }

            override fun unlock(owner: Any?) = sema.release()
        }
    }

    @Test
    override fun testUnconfinedStackOverflow() {
        // TODO: remove this override once it is fixed
        assertFails {
            super.testUnconfinedStackOverflow()
        }
    }

    @Test
    override fun holdLock() {
        // semaphores don't track owners
        assertFailsWith(NotImplementedError::class) {
            super.holdLock()
        }
    }
}
