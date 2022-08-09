import kotlinx.coroutines.*
import kotlinx.coroutines.test.*
import java.lang.ref.*
import kotlin.test.*

class TestCoroutineSchedulerJvmTest {

    /**
     * This test demonstrates a bug in the TestCoroutineScheduler implementation: canceled delayed
     * jobs are held in memory by TestCoroutineScheduler until the TestCoroutineScheduler current
     * time has moved past the job's planned time, even though said job has long been canceled.
     *
     * Canceled jobs should instead be immediately removed from TestCoroutineScheduler#events.
     */
    @Test
    fun testCancellationLeakInTestCoroutineScheduler() = runTest {
        lateinit var weakRef: WeakReference<*>
        val delayedLeakingJob = launch {
            val leakingObject = Any()
            weakRef = WeakReference(leakingObject)
            // This delay prevents the job from finishing.
            delay(3)
            // This is never called as job is canceled before we get here. However this code
            // holds a reference to leakingObject, preventing it from becoming weakly reachable
            // until the job itself is weakly reachable.
            println(leakingObject)
        }

        // Start running the job and hit delay.
        advanceTimeBy(1)

        // At this point, delayedLeakingJob is still in the queue and holding on to leakingObject.
        System.gc()
        assertNotNull(weakRef.get())

        // We're canceling the job, and now expect leakingObject to become weakly reachable.
        delayedLeakingJob.cancel()

        // Surprise: the canceled job is not weakly reachable! TestCoroutineScheduler is holding
        // on to it in its TestCoroutineScheduler#events queue.
        System.gc()
        assertNotNull(weakRef.get())

        // Let's move time forward without going over the delay yet.
        advanceTimeBy(1)

        // Still not weakly reachable.
        System.gc()
        assertNotNull(weakRef.get())

        // Now we move past the delay
        advanceTimeBy(2)

        // The job is finally weakly reachable and leakingObject is released.
        System.gc()
        assertNull(weakRef.get())
    }
}