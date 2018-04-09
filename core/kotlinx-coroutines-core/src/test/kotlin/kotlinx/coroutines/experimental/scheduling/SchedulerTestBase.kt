package kotlinx.coroutines.experimental.scheduling

import kotlinx.atomicfu.atomic
import kotlinx.coroutines.experimental.*
import org.junit.After
import kotlin.coroutines.experimental.CoroutineContext

abstract class SchedulerTestBase : TestBase() {
    companion object {
        val CORES_COUNT = Runtime.getRuntime().availableProcessors()

        fun checkPoolThreads(expectedThreadsCount: Int = Runtime.getRuntime().availableProcessors()) {
            val actual = Thread.getAllStackTraces().keys.count { it is CoroutineScheduler.PoolWorker }
            require(actual == expectedThreadsCount, { "Expected $expectedThreadsCount pool threads, but have $actual" })
        }

        fun checkPoolThreads(range: IntRange) {
            val actual = Thread.getAllStackTraces().keys.count { it is CoroutineScheduler.PoolWorker }
            require(actual in range, { "Expected pool threads to be in interval $range, but have $actual" })
        }

        suspend fun Iterable<Job>.joinAll() = forEach { it.join() }
    }

    private var exception = atomic<Throwable?>(null)
    private val handler = CoroutineExceptionHandler({ _, e -> exception.value = e })

    protected var corePoolSize = 1

    private var _dispatcher: ExperimentalCoroutineDispatcher? = null
    protected val dispatcher: CoroutineContext
        get() {
            if (_dispatcher == null) {
                _dispatcher = ExperimentalCoroutineDispatcher(corePoolSize)
            }

            return _dispatcher!! + handler
        }

    protected var blockingDispatcher = lazy {
        blockingDispatcher(1000)
    }

    protected fun blockingDispatcher(parallelism: Int): CoroutineContext {
        val intitialize = dispatcher
        return _dispatcher!!.blocking(parallelism) + handler
    }

    @After
    fun after() {
        runBlocking {
            withTimeout(5_000) {
                _dispatcher?.close()
            }
        }
        exception.value?.let { throw it }
    }
}