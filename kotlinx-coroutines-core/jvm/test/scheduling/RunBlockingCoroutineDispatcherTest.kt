package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import org.junit.*
import java.util.concurrent.atomic.*

class RunBlockingCoroutineDispatcherTest : SchedulerTestBase() {
    @Test
    fun testRecursiveRunBlockingCanExceedDefaultDispatcherLimit() {
        val maxDepth = CORES_COUNT * 3 + 3
        fun body(depth: Int) {
            if (depth == maxDepth) return
            runBlocking(Dispatchers.Default) {
                launch(Dispatchers.Default) {
                    body(depth + 1)
                }
            }
        }

        body(1)
        checkPoolThreadsCreated(maxDepth..maxDepth + 1)
    }

    @Test
    fun testNoDefaultDispatcherStarvationWithRunBlocking() = testRunBlockingCanExceedDispatchersLimit(dispatcher, CORE_POOL_SIZE * 3 + 3)

    @Test
    fun testNoIoDispatcherStarvationWithRunBlocking() = testRunBlockingCanExceedDispatchersLimit(blockingDispatcher(2), 5)

    private fun testRunBlockingCanExceedDispatchersLimit(targetDispatcher: CoroutineDispatcher, threadsToReach: Int) {
        val barrier = CompletableDeferred<Unit>()
        val count = AtomicInteger(0)
        fun blockingCode() {
            runBlocking {
                count.incrementAndGet()
                barrier.await()
                count.decrementAndGet()
            }
        }
        runBlocking {
            repeat(threadsToReach) {
                launch(targetDispatcher) {
                    blockingCode()
                }
            }
            while (count.get() != threadsToReach) {
                Thread.sleep(1)
            }
            async(targetDispatcher) {
                yield()
                42
            }.join()
            barrier.complete(Unit)
            while (count.get() != 0) {
                Thread.sleep(1)
            }
        }
    }
}