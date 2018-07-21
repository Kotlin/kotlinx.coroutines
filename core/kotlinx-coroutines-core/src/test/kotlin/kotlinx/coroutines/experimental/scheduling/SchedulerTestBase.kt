package kotlinx.coroutines.experimental.scheduling

import kotlinx.atomicfu.*
import kotlinx.coroutines.experimental.*
import org.junit.*
import kotlin.coroutines.experimental.*

abstract class SchedulerTestBase : TestBase() {
    companion object {
        val CORES_COUNT = Runtime.getRuntime().availableProcessors()

        /**
         * Asserts that [expectedThreadsCount] pool worker threads were created.
         * Note that 'created' doesn't mean 'exists' because pool supports dynamic shrinking
         */
        fun checkPoolThreadsCreated(expectedThreadsCount: Int = CORES_COUNT) {
            val threadsCount = maxSequenceNumber()!!
            require(threadsCount == expectedThreadsCount)
                { "Expected $expectedThreadsCount pool threads, but has $threadsCount" }
        }

        /**
         * Asserts that any number of pool worker threads in [range] were created.
         * Note that 'created' doesn't mean 'exists' because pool supports dynamic shrinking
         */
        fun checkPoolThreadsCreated(range: IntRange) {
            val maxSequenceNumber = maxSequenceNumber()!!
            require(maxSequenceNumber in range) { "Expected pool threads to be in interval $range, but has $maxSequenceNumber" }
        }

        /**
         * Asserts that any number of pool worker threads in [range] exists at the time of method invocation
         */
        fun checkPoolThreadsExist(range: IntRange) {
            val threads = Thread.getAllStackTraces().keys.filter { it is CoroutineScheduler.Worker }.count()
            require(threads in range) { "Expected threads in $range interval, but has $threads" }
        }

        /**
         * Asserts that [expectedThreadsCount] of pool worker threads exists at the time of method invocation
         */
        fun checkPoolThreadsExist(expectedThreadsCount: Int = CORES_COUNT) {
            val threads = Thread.getAllStackTraces().keys.filter { it is CoroutineScheduler.Worker }.count()
            require(threads == expectedThreadsCount) { "Expected $expectedThreadsCount threads, but has $threads" }
        }

        fun initialPoolSize() = 1

        private fun maxSequenceNumber(): Int? {
            return Thread.getAllStackTraces().keys.filter { it is CoroutineScheduler.Worker }
                .map { sequenceNumber(it.name) }.max()
        }

        private fun sequenceNumber(threadName: String): Int {
            val suffix = threadName.substring(threadName.lastIndexOf("-") + 1)
            val separatorIndex = suffix.indexOf(' ')
            if (separatorIndex == -1) {
                return suffix.toInt()
            }

            return suffix.substring(0, separatorIndex).toInt()
        }

        suspend fun Iterable<Job>.joinAll() = forEach { it.join() }
    }

    private var exception = atomic<Throwable?>(null)
    private val handler = CoroutineExceptionHandler({ _, e -> exception.value = e })

    protected var corePoolSize = 1
    protected var maxPoolSize = 1024


    private var _dispatcher: ExperimentalCoroutineDispatcher? = null
    protected val dispatcher: CoroutineContext
        get() {
            if (_dispatcher == null) {
                _dispatcher = ExperimentalCoroutineDispatcher(corePoolSize, maxPoolSize)
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

    fun initialPoolSize() = corePoolSize.coerceAtMost(2)

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