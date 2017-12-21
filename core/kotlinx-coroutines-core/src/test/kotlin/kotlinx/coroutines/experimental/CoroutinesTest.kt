package kotlinx.coroutines.experimental

import kotlin.test.*

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

    private class TestException() : Exception()
}