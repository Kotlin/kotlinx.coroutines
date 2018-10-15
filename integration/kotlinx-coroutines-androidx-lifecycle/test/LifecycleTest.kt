package kotlinx.coroutines.experimental.androidx.lifecycle

import androidx.lifecycle.Lifecycle
import androidx.lifecycle.LifecycleOwner
import androidx.lifecycle.LifecycleRegistry
import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.TestBase
import kotlin.coroutines.experimental.suspendCoroutine
import kotlin.test.*

class LifecycleTest : TestBase() {

    @Test
    fun testLifecycleDefaultScopeUsesDefaultJob() = runTest {
        val lifecycle = TestLifecycleOwner().lifecycle
        lifecycle.markState(Lifecycle.State.CREATED)
        val lifecycleJob = lifecycle.job
        val lifecycleScopeJob = lifecycle.coroutineScope.coroutineContext[Job]
        assertSame(lifecycleJob, lifecycleScopeJob)
        lifecycle.markState(Lifecycle.State.DESTROYED)
    }

    @Test
    fun testLifecycleJobIsCached() = runTest {
        val lifecycle = TestLifecycleOwner().lifecycle
        lifecycle.markState(Lifecycle.State.CREATED)
        assertSame(lifecycle.job, lifecycle.job)
        lifecycle.markState(Lifecycle.State.DESTROYED)
    }

    @Test
    fun testLifecycleOnDestroyCancelsJob() = runTest {
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
    fun testAlreadyDestroyedLifecycleMakesCancelledJob() = runTest {
        val lifecycle = TestLifecycleOwner().lifecycle
        lifecycle.markState(Lifecycle.State.CREATED)
        lifecycle.markState(Lifecycle.State.DESTROYED)
        val job = lifecycle.job
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
