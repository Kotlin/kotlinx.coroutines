package kotlinx.coroutines.experimental.scheduling

import kotlinx.coroutines.experimental.TestBase
import org.junit.After
import org.junit.Test
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.CountDownLatch
import java.util.concurrent.atomic.AtomicInteger
import kotlin.coroutines.experimental.CoroutineContext
import kotlin.coroutines.experimental.EmptyCoroutineContext
import kotlin.test.assertEquals

class CoroutineSchedulerStressTest : TestBase() {

    private var dispatcher: ExperimentalCoroutineDispatcher = ExperimentalCoroutineDispatcher()
    private val observedThreads = ConcurrentHashMap<Thread, MutableSet<Int>>()
    private val tasksNum = 1_000_000
    private val processed = AtomicInteger(0)

    @After
    fun tearDown() {
        dispatcher.close()
    }

    @Test
    fun submitTasks() {
        stressTest(ForkedMarker)
    }

    @Test
    fun submitTasksForked() {
        stressTest(EmptyCoroutineContext)
    }

    private fun stressTest(ctx: CoroutineContext) {
        val finishLatch = CountDownLatch(1)

        for (i in 1..tasksNum) {
            dispatcher.dispatch(ctx, Runnable {
                val numbers = observedThreads.computeIfAbsent(Thread.currentThread(), { _ -> hashSetOf() })
                require(numbers.add(i))
                if (processed.incrementAndGet() == tasksNum) {
                    finishLatch.countDown()
                }
            })
        }

        finishLatch.await()
        assertEquals(Runtime.getRuntime().availableProcessors(), observedThreads.size)
        val result = observedThreads.values.flatMap { it }.toSet()
        assertEquals((1..tasksNum).toSet(), result)
    }
}
