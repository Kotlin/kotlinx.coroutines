package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.coroutines.*
import kotlin.test.*

class JobExtensionsTest : TestBase() {

    private val job = Job()
    private val scope = CoroutineScope(job + CoroutineExceptionHandler { _, _ ->  })

    @Test
    fun testIsActive() = runTest {
        expect(1)
        scope.launch(Dispatchers.Unconfined) {
            ensureActive()
            coroutineContext.ensureActive()
            coroutineContext[Job]!!.ensureActive()
            expect(2)
            delay(Long.MAX_VALUE)
        }

        expect(3)
        job.ensureActive()
        scope.ensureActive()
        scope.coroutineContext.ensureActive()
        job.cancelAndJoin()
        finish(4)
    }

    @Test
    fun testIsCompleted() = runTest {
        expect(1)
        scope.launch(Dispatchers.Unconfined) {
            ensureActive()
            coroutineContext.ensureActive()
            coroutineContext[Job]!!.ensureActive()
            expect(2)
        }

        expect(3)
        job.complete()
        job.join()
        assertFailsWith<JobCancellationException> { job.ensureActive() }
        assertFailsWith<JobCancellationException> { scope.ensureActive() }
        assertFailsWith<JobCancellationException> { scope.coroutineContext.ensureActive() }
        finish(4)
    }


    @Test
    fun testIsCancelled() = runTest {
        expect(1)
        scope.launch(Dispatchers.Unconfined) {
            ensureActive()
            coroutineContext.ensureActive()
            coroutineContext[Job]!!.ensureActive()
            expect(2)
            throw TestException()
        }

        expect(3)
        checkException { job.ensureActive() }
        checkException { scope.ensureActive() }
        checkException { scope.coroutineContext.ensureActive() }
        finish(4)
    }

    @Test
    fun testEnsureActiveWithEmptyContext() = runTest {
        withEmptyContext {
            ensureActive() // should not do anything
        }
    }

    private inline fun checkException(block: () -> Unit) {
        val result = runCatching(block)
        val exception = result.exceptionOrNull() ?: fail()
        assertIs<JobCancellationException>(exception)
        assertIs<TestException>(exception.cause)
    }

    @Test
    fun testJobExtension() = runTest {
        assertSame(coroutineContext[Job]!!, coroutineContext.job)
        assertSame(NonCancellable, NonCancellable.job)
        assertSame(job, job.job)
        assertFailsWith<IllegalStateException> { EmptyCoroutineContext.job }
        assertFailsWith<IllegalStateException> { Dispatchers.Default.job }
        assertFailsWith<IllegalStateException> { (Dispatchers.Default + CoroutineName("")).job }
    }
}
