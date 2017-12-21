package kotlinx.coroutines.experimental

import org.junit.Test

class CoroutinesTest : TestBase() {
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

    @Test
    fun testCancelManyCompletedAttachedChildren() = runTest {
        val parent = launch(coroutineContext) { /* do nothing */ }
        val n = 10_000 * stressTestMultiplier
        repeat(n) {
            // create a child that already completed
            val child = launch(coroutineContext, CoroutineStart.UNDISPATCHED) { /* do nothing */ }
            // attach it manually
            parent.attachChild(child)
        }
        parent.cancelAndJoin() // cancel parent, make sure no stack overflow
    }

    private fun throwTestException(): Unit = throw TestException()

    private class TestException : Exception {
        constructor(message: String): super(message)
        constructor(): super()
    }
}