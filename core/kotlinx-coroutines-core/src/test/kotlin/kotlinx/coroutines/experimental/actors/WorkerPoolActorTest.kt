package kotlinx.coroutines.experimental.actors

import kotlinx.coroutines.experimental.*
import org.junit.Test
import org.mockito.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

class WorkerPoolActorTest : TestBase() {

    private val parallelism = 8

    @Test
    fun testDistribution() = runTest {
        val accumulator = mutableMapOf<Int, Int>()
        val worker = worker(accumulator, coroutineContext)

        repeat(100_000) {
            worker.send()
        }

        worker.close()
        worker.join()

        for (i in 1..parallelism) {
            assertTrue(accumulator[i]!! > 10_000)
        }
    }

    @Test
    fun testLazyStart() = runTest {
        val worker = workerPoolActor<Int>(parallelism, coroutineContext) {
            expect(it)
        }

        expect(1)
        worker.send(239)
        worker.send(239)
        worker.send(239)
        worker.kill()
        worker.join()
        finish(2)
    }

    @Test
    fun testInvalidMock() = runTest(expected = { it is IllegalStateException }) {
        workerPool(parallelism) {
            Mockito.mock(TestActor::class.java)
        }
    }

    private fun worker(
        accumulator: MutableMap<Int, Int>,
        context: CoroutineContext
    ): TestActor {
        var id = 0
        return workerPool(parallelism) {
            TestActor(id++, accumulator, context)
        }
    }

    private open class TestActor(val id: Int, val map: MutableMap<Int, Int>, context: CoroutineContext) :
        WorkerPoolActor<TestActor>(context) {

        suspend fun send() = act {
            val counter = map[id] ?: 0
            map[id] = counter + 1
        }
    }
}
