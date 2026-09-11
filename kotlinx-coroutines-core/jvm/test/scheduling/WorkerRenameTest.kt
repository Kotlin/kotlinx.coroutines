package kotlinx.coroutines.scheduling

import kotlinx.coroutines.testing.*
import org.junit.Test
import java.lang.Runnable
import java.util.concurrent.*
import java.util.concurrent.atomic.*
import kotlin.test.*

/**
 * Regression test for #2234: renaming a live worker thread from a different
 * thread can require the runtime to suspend it first, which can time out and
 * crash the process (see CoroutineScheduler.Worker.indexInArray). Verifies
 * that a cross-thread indexInArray change never renames the thread directly,
 * and that the worker corrects its own name once it next runs.
 */
class WorkerRenameTest : TestBase() {

    @Test
    fun testCrossThreadIndexChangeDoesNotRenameLiveWorker() {
        CoroutineScheduler(1, 2, schedulerName = "WorkerRenameTest").use { scheduler ->
            val workerRef = AtomicReference<CoroutineScheduler.Worker>()
            val started = CountDownLatch(1)
            val release = CountDownLatch(1)

            scheduler.dispatch(Runnable {
                workerRef.set(Thread.currentThread() as CoroutineScheduler.Worker)
                started.countDown()
                release.await()
            })
            started.await()
            val worker = workerRef.get()

            try {
                val nameBefore = worker.name
                val otherIndex = worker.indexInArray + 1000
                worker.indexInArray = otherIndex // cross-thread: this is the test thread, not `worker`
                assertEquals(nameBefore, worker.name, "cross-thread rename must not happen synchronously")
            } finally {
                release.countDown()
            }

            val expectedName = "WorkerRenameTest-worker-${worker.indexInArray}"
            val deadline = System.currentTimeMillis() + 5_000
            while (worker.name != expectedName && System.currentTimeMillis() < deadline) {
                Thread.sleep(10)
            }
            assertEquals(expectedName, worker.name, "worker should self-heal its own name once it runs again")
        }
    }

    @Test
    fun testSelfRenameHappensSynchronously() {
        CoroutineScheduler(1, 2, schedulerName = "WorkerRenameTest").use { scheduler ->
            val done = CountDownLatch(1)
            var expectedName: String? = null
            var nameAfterSelfRename: String? = null

            scheduler.dispatch(Runnable {
                val self = Thread.currentThread() as CoroutineScheduler.Worker
                self.indexInArray = self.indexInArray + 1000 // same-thread: self-rename
                expectedName = "WorkerRenameTest-worker-${self.indexInArray}"
                nameAfterSelfRename = self.name // must already reflect the change, synchronously
                done.countDown()
            })

            done.await()
            assertEquals(expectedName, nameAfterSelfRename, "self-rename must apply synchronously, not deferred")
        }
    }
}
