package kotlinx.coroutines.experimental.scheduling

import kotlinx.coroutines.experimental.*
import org.junit.After
import org.junit.Test
import java.util.concurrent.atomic.AtomicBoolean
import kotlin.test.assertEquals
import kotlin.test.assertNull

class CoroutineSchedulerTest : TestBase() {

    var dispatcher: ExperimentalCoroutineDispatcher? = null

    @After
    fun tearDown() {
        schedulerTimeSource = NanoTimeSource
        dispatcher?.close()
    }

    @Test
    fun testSingleThread() = runBlocking {
        dispatcher = ExperimentalCoroutineDispatcher(1)
        expect(1)
        withContext(dispatcher!!) {
            require(Thread.currentThread().name.contains("CoroutinesScheduler-worker"))
            expect(2)
            val job = async(coroutineContext) {
                expect(3)
                delay(10)
                expect(4)
            }

            job.await()
            expect(5)
        }

        finish(6)
    }

    @Test
    fun testStealing() = runBlocking {
        dispatcher = ExperimentalCoroutineDispatcher(2)
        val flag = AtomicBoolean(false)
        val job = async(context = dispatcher!!) {
            expect(1)
            val innerJob = async {
                expect(2)
                flag.set(true)
            }

            while (!flag.get()) {
                Thread.yield() // Block current thread, submitted inner job will be stolen
            }

            innerJob.await()
            expect(3)
        }

        job.await()
        finish(4)
    }

    @Test
    fun testNoStealing() = runBlocking {
        dispatcher = ExperimentalCoroutineDispatcher()
        schedulerTimeSource = TestTimeSource(0L)
        withContext(dispatcher!!) {
            val thread = Thread.currentThread()
            val job = async(dispatcher!!) {
                assertEquals(thread, Thread.currentThread())
                val innerJob = async(dispatcher!!) {
                    assertEquals(thread, Thread.currentThread())
                }
                innerJob.await()
            }

            job.await()
            assertEquals(thread, Thread.currentThread())
        }
    }

    @Test
    fun testDelay() = runBlocking {
        dispatcher = ExperimentalCoroutineDispatcher(2)
        withContext(dispatcher!!) {
            expect(1)
            delay(10)
            expect(2)
        }

        finish(3)
    }

    @Test
    fun testWithTimeout() = runBlocking {
        dispatcher = ExperimentalCoroutineDispatcher()
        withContext(dispatcher!!) {
            expect(1)
            val result = withTimeoutOrNull(1000) {
                expect(2)
                yield() // yield only now
                "OK"
            }
            assertEquals("OK", result)

            val nullResult = withTimeoutOrNull(1000) {
                expect(3)
                while (true) {
                    yield()
                }

                "OK"
            }

            assertNull(nullResult)
            finish(4)
        }
    }

    @Test
    fun testRngUniformDistribution() {
        CoroutineScheduler(1).use { scheduler ->
            val worker = scheduler.PoolWorker(1)
            testUniformDistribution(worker, 2)
            testUniformDistribution(worker, 4)
            testUniformDistribution(worker, 8)
            testUniformDistribution(worker, 12)
            testUniformDistribution(worker, 16)
        }
    }

    private fun testUniformDistribution(worker: CoroutineScheduler.PoolWorker, bound: Int) {
        val result = IntArray(bound)
        val iterations = 10_000_000
        repeat(iterations) {
            ++result[worker.nextInt(bound)]
        }

        val bucketSize = iterations / bound
        for (i in result) {
            val ratio = i.toDouble() / bucketSize
            // 10% deviation
            check(ratio <= 1.1)
            check(ratio >= 0.9)
        }
    }
}
