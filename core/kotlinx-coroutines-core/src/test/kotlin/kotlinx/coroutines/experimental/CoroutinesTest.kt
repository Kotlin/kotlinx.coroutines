package kotlinx.coroutines.experimental

import org.junit.Test

class CoroutinesTest : TestBase() {
    @Test
    fun testParentCrashCancelsChildren() = runTest(
        unhandled = listOf({ it -> it is TestException })
    ) {
        expect(1)
        val parent = launch(coroutineContext + Job()) {
            expect(4)
            throw TestException("Crashed")
        }
        launch(coroutineContext + parent, CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                yield() // to test
            } finally {
                expect(5)
                withContext(NonCancellable) { yield() } // to test
                expect(7)
            }
            expectUnreached() // will get cancelled, because parent crashes
        }
        expect(3)
        yield() // to parent
        expect(6)
        parent.join() // make sure crashed parent still waits for its child
        finish(8)
    }

    @Test
    fun testNotCancellableCodeWithExceptionCancelled() = runTest {
        expect(1)
        // CoroutineStart.ATOMIC makes sure it will not get cancelled for it starts executing
        val job = launch(start = CoroutineStart.ATOMIC) {
            Thread.sleep(100) // cannot be cancelled
            throwTestException() // will throw
            expectUnreached()
        }
        expect(2)
        job.cancel()
        finish(3)
    }

    @Test
    fun testNotCancellableChildWithExceptionCancelled() = runTest(
        expected = { it is TestException }
    ) {
        expect(1)
        // CoroutineStart.ATOMIC makes sure it will not get cancelled for it starts executing
        val d = async(coroutineContext, start = CoroutineStart.ATOMIC) {
            finish(4)
            throwTestException() // will throw
            expectUnreached()
        }
        expect(2)
        // now cancel with some other exception
        d.cancel(IllegalArgumentException())
        // now await to see how it got crashed -- IAE should have been suppressed by TestException
        expect(3)
        d.await()
    }

    private fun throwTestException(): Unit = throw TestException()

    private class TestException : Exception {
        constructor(message: String): super(message)
        constructor(): super()
    }
}