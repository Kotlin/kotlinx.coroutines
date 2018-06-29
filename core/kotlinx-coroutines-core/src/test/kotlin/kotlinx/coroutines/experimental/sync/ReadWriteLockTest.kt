package kotlinx.coroutines.experimental.sync

import kotlin.coroutines.experimental.*
import kotlin.test.*
import kotlinx.coroutines.experimental.TestBase
import kotlinx.coroutines.experimental.launch
import kotlinx.coroutines.experimental.yield

class ReadWriteLockTest : TestBase() {

    private val rw: ReadWriteLock = ReadWriteLock()

    @Test
    fun testWriteSuspendsRead() { testLockSimple(rw.write, rw.read) }

    @Test
    fun testReadSuspendsWrite() { testLockSimple(rw.read, rw.write) }

    @Test
    fun testWriteSuspendsWrite() { testLockSimple(rw.write, rw.write) }

    private fun testLockSimple(lock1: Lock, lock2: Lock) = runTest {
        launch(coroutineContext) {
            expect(3)

            lock2.lock() // suspends

            expect(6)
            lock2.unlock()
            expect(7)
        }

        expect(1)
        lock1.lock()
        expect(2)

        yield()

        expect(4)
        lock1.unlock()
        expect(5)

        yield()

        finish(8)
    }

    @Test
    fun testMultipleReaders() = runTest {
        launch(coroutineContext) {
            expect(3)
            rw.read.lock() // does not suspend
            rw.read.unlock()
            expect(4)
        }

        expect(1)
        rw.read.lock()
        expect(2)

        yield()

        expect(5)
        rw.read.unlock()
        yield()
        finish(6)
    }

    @Test
    fun testLockWriteTryRead() { testTryLockSimple(rw.write, rw.read) }

    @Test
    fun testLockReadTryWrite() { testTryLockSimple(rw.read, rw.write) }

    @Test
    fun testLockWriteTryWrite() { testTryLockSimple(rw.write, rw.write) }

    private fun testTryLockSimple(toLock: Lock, toTry: Lock) = runTest {
        launch(coroutineContext) {
            expect(2)
            toLock.lock()
            expect(3)

            yield()

            expect(6)
            toLock.unlock()
            expect(7)
        }

        expect(1)

        yield()

        expect(4)
        assertFalse(toTry.tryLock())
        expect(5)

        yield()

        expect(8)
        assertTrue(toTry.tryLock())
        toTry.unlock()
        finish(9)
    }

    @Test
    fun testLockReadTryRead() = runTest {
        launch(coroutineContext) {
            expect(3)
            rw.read.lock()
            expect(4)

            yield()

            expect(7)
            rw.read.unlock()
            expect(8)
        }

        expect(1)
        assertTrue(rw.read.tryLock())
        rw.read.unlock()
        expect(2)

        yield()

        expect(5)
        assertTrue(rw.read.tryLock())
        rw.read.unlock()
        expect(6)

        yield()

        finish(9)
    }

    @Test
    fun testWriteReadNonReentrant() { testNonReentrant(rw.write, rw.read) }

    @Test
    fun testReadWriteNonReentrant() { testNonReentrant(rw.read, rw.write) }

    @Test
    fun testWriteWriteNonReentrant() { testNonReentrant(rw.write, rw.write) }

    private fun testNonReentrant(lock1: Lock, lock2: Lock) = runTest {
        launch(coroutineContext) {
            expect(3)
            lock1.unlock()
            expect(4)
        }

        expect(1)
        lock1.lock()
        expect(2)

        lock2.lock() // suspend

        expect(5)
        lock2.unlock()
        finish(6)
    }

    @Test
    fun testReenteringReadRequiresReleaving() = runTest {
        launch(coroutineContext) {
            expect(3)

            rw.write.lock() // suspend

            expect(6)
            rw.write.unlock()
            expect(7)
        }

        expect(1)
        rw.read.lock()
        rw.read.lock()
        rw.read.unlock()
        expect(2)

        yield()

        expect(4)
        rw.read.unlock()
        expect(5)

        yield()

        finish(8)
    }

    @Test
    fun testWriteReadWriteFairness() { testFairness(rw.write, rw.read) }

    @Test
    fun testReadWriteReadFairness() { testFairness(rw.read, rw.write) }

    private fun testFairness(lock1: Lock, lock2: Lock) = runTest {
        launch(coroutineContext) {
            // second to lock
            expect(3)

            lock2.lock() // suspend

            expect(7)
            lock2.unlock()
            expect(8)
        }

        launch(coroutineContext) {
            // third to lock
            expect(4)

            lock1.lock() // suspend

            expect(9)
            lock1.unlock()
            expect(10)
        }

        // first to lock
        expect(1)
        lock1.lock()
        expect(2)

        yield()

        expect(5)
        lock1.unlock()
        expect(6)

        yield()
        yield()

        finish(11)
    }
}
