package kotlinx.coroutines.experimental.androidx.lifecycle

import androidx.lifecycle.GenericLifecycleObserver
import androidx.lifecycle.Lifecycle
import androidx.lifecycle.LifecycleOwner
import androidx.lifecycle.LifecycleRegistry
import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.suspendCoroutine
import kotlin.test.*

class LifecycleTest : TestBase() {

    @Test
    fun `Test lifecycle default scope uses default job`() = runTest {
        val lifecycle = TestLifecycleOwner().lifecycle
        lifecycle.markState(Lifecycle.State.CREATED)
        val lifecycleJob = lifecycle.job
        val lifecycleScopeJob = lifecycle.coroutineScope.coroutineContext[Job]
        assertSame(lifecycleJob, lifecycleScopeJob)
        lifecycle.markState(Lifecycle.State.DESTROYED)
    }

    @Test
    fun `Test lifecycle job is cached`() = runTest {
        val lifecycle = TestLifecycleOwner().lifecycle
        lifecycle.markState(Lifecycle.State.CREATED)
        assertSame(lifecycle.job, lifecycle.job)
        lifecycle.markState(Lifecycle.State.DESTROYED)
    }

    @Test
    fun `Test lifecycle on destroy cancels job`() = runTest {
        val lifecycle = TestLifecycleOwner().lifecycle
        lifecycle.markState(Lifecycle.State.CREATED)
        val job = lifecycle.job
        assertTrue(job.isActive)
        assertFalse(job.isCancelled)
        lifecycle.markState(Lifecycle.State.STARTED)
        lifecycle.markState(Lifecycle.State.RESUMED)
        assertTrue(job.isActive)
        assertFalse(job.isCancelled)
        lifecycle.markState(Lifecycle.State.DESTROYED)
        suspendCoroutine<Unit> { c ->
            job.invokeOnCompletion { c.resume(Unit) }
        }
        assertTrue(job.isCancelled)
        assertFalse(job.isActive)
    }

    @Test
    fun `Test already destroyed lifecycle makes cancelled job`() = runTest {
        val lifecycle = TestLifecycleOwner().lifecycle
        lifecycle.markState(Lifecycle.State.CREATED)
        lifecycle.markState(Lifecycle.State.DESTROYED)
        val job = lifecycle.job
        assertFalse(job.isActive)
        assertTrue(job.isCancelled)
    }

    @Test
    fun `Test lifecycle owner scope is lifecycle scope`() = runTest {
        val lifecycleOwner = TestLifecycleOwner()
        val lifecycle = lifecycleOwner.lifecycle
        assertSame(lifecycle.coroutineScope, lifecycleOwner.coroutineScope)
    }

    @Test
    fun `Test scope is not active after destroy`() = runTest {
        val lifecycle = TestLifecycleOwner().lifecycle
        lifecycle.markState(Lifecycle.State.CREATED)
        lifecycle.markState(Lifecycle.State.STARTED)
        val scope = lifecycle.createScope(Lifecycle.State.STARTED)
        expect(1)
        val testJob = scope.launch {
            try {
                expect(2)
                delay(Long.MAX_VALUE)
                expectUnreached()
            } catch (e: CancellationException) {
                expect(3)
                throw e
            } finally {
                expect(4)
            }
        }
        lifecycle.markState(Lifecycle.State.CREATED)
        testJob.join()
        finish(5)
        assertFalse(scope.isActive)
        lifecycle.markState(Lifecycle.State.DESTROYED)
    }

    @Test
    fun `Test observer is called after destroy`() = runTest {
        val lifecycle = TestLifecycleOwner().lifecycle
        lifecycle.markState(Lifecycle.State.CREATED)
        val activeWhile = Lifecycle.State.INITIALIZED
        val job = with(lifecycle) {
            Job().also { job ->
                addObserver(object : GenericLifecycleObserver {
                    override fun onStateChanged(source: LifecycleOwner?, event: Lifecycle.Event) {
                        if (!currentState.isAtLeast(activeWhile)) {
                            removeObserver(this)
                            job.cancel()
                        }
                    }
                })
            }
        }
        assertTrue(job.isActive)
        assertFalse(job.isCancelled)
        lifecycle.markState(Lifecycle.State.DESTROYED)
        job.join()
        assertFalse(job.isActive)
        assertTrue(job.isCancelled)
    }

    @AfterTest
    fun closeTestMainDispatcher() {
        TestMainDispatcher.default.close()
    }

    private class TestLifecycleOwner : LifecycleOwner {
        override fun getLifecycle() = LifecycleRegistry(this)
    }
}
