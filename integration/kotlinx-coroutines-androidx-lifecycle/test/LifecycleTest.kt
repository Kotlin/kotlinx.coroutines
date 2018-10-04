package kotlinx.coroutines.androidx.lifecycle

import androidx.lifecycle.Lifecycle
import androidx.lifecycle.LifecycleOwner
import androidx.lifecycle.LifecycleRegistry
import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.TestBase
import kotlin.test.*

class LifecycleTest : TestBase() {

    @BeforeTest
    fun setupMainThread() {
        TODO("Add RoboElectric and kotlinx-coroutines-android dependencies")
        //TODO: Check if setting up main thread is really needed
    }

    @Test fun testLifecycleDefaultScopeUsesDefaultJob() = runTest {
        val lifecycle = TestLifecycleOwner().lifecycle
        val lifecycleJob = lifecycle.job
        val lifecycleScopeJob = lifecycle.coroutineScope.coroutineContext[Job]
        assertSame(lifecycleJob, lifecycleScopeJob)
        lifecycle.markState(Lifecycle.State.DESTROYED)
    }

    @Test fun testLifecycleJobIsCached() = runTest {
        val lifecycle = TestLifecycleOwner().lifecycle
        assertSame(lifecycle.job, lifecycle.job)
        lifecycle.markState(Lifecycle.State.DESTROYED)
    }

    @Test fun testLifecycleOnDestroyCancelsJob() = runTest {
        val lifecycle = TestLifecycleOwner().lifecycle
        lifecycle.markState(Lifecycle.State.CREATED)
        val job = lifecycle.job
        assertTrue(job.isActive)
        assertFalse(job.isCancelled)
        lifecycle.markState(Lifecycle.State.DESTROYED)
        assertFalse(job.isActive)
        assertTrue(job.isCancelled)
    }

    @Test fun testAlreadyDestroyedLifecycleMakesCancelledJob() = runTest {
        val lifecycle = TestLifecycleOwner().lifecycle
        lifecycle.markState(Lifecycle.State.DESTROYED)
        val job = lifecycle.job
        assertFalse(job.isActive)
        assertTrue(job.isCancelled)
    }

    private class TestLifecycleOwner : LifecycleOwner {
        override fun getLifecycle() = LifecycleRegistry(this)
    }
}
