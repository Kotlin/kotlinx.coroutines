@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.test.*

// see https://github.com/Kotlin/kotlinx.coroutines/issues/585
class FailedJobTest : TestBase() {
    @Test
    fun testCancelledJob() = runTest {
        expect(1)
        val job = launch {
            expectUnreached()
        }
        expect(2)
        job.cancelAndJoin()
        finish(3)
        assertTrue(job.isCompleted)
        assertTrue(!job.isActive)
        assertTrue(job.isCancelled)
    }

    @Test
    fun testFailedJob() = runTest(
        unhandled = listOf({it -> it is TestException })
    ) {
        expect(1)
        val job = launch(NonCancellable) {
            expect(3)
            throw TestException()
        }
        expect(2)
        job.join()
        finish(4)
        assertTrue(job.isCompleted)
        assertTrue(!job.isActive)
        assertTrue(job.isCancelled)
    }

    @Test
    fun testFailedChildJob() = runTest(
        unhandled = listOf({it -> it is TestException })
    ) {
        expect(1)
        val job = launch(NonCancellable) {
            expect(3)
            launch {
                throw TestException()
            }
        }
        expect(2)
        job.join()
        finish(4)
        assertTrue(job.isCompleted)
        assertTrue(!job.isActive)
        assertTrue(job.isCancelled)
    }
}