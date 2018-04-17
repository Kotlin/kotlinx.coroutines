package kotlinx.coroutines.experimental

import org.junit.*
import java.io.*
import java.util.concurrent.*
import kotlin.coroutines.experimental.*

class WithContextCancellationStressTest : TestBase() {

    private val iterations = 150_000 * stressTestMultiplier
    private val pool = newFixedThreadPoolContext(3, "WithContextCancellationStressTest")

    @After
    fun tearDown() {
        pool.close()
    }

    @Test
    fun testConcurrentCancellation() = runBlocking {
        var ioException = 0
        var arithmeticException = 0
        var aioobException = 0

        repeat(iterations) {
            val barrier = CyclicBarrier(4)
            val jobWithContext = async(pool) {
                barrier.await()
                withContext(wrapperDispatcher(coroutineContext)) {
                    throw IOException()
                }
            }

            val cancellerJob = async(pool) {
                barrier.await()
                jobWithContext.cancel(ArithmeticException())
            }

            val cancellerJob2 = async(pool) {
                barrier.await()
                jobWithContext.cancel(ArrayIndexOutOfBoundsException())
            }

            barrier.await()
            val c1 = cancellerJob.await()
            val c2 = cancellerJob2.await()
            require(!(c1 && c2)) { "Same job cannot be cancelled twice" }

            try {
                jobWithContext.await()
            } catch (e: Exception) {
                when (e) {
                    is IOException -> ++ioException
                    is JobCancellationException -> {
                        val cause = e.cause
                        when (cause) {
                            is ArithmeticException -> ++arithmeticException
                            is ArrayIndexOutOfBoundsException -> ++aioobException
                            else -> error("Unexpected exception")
                        }
                    }
                    else -> error("Unexpected exception $e")
                }
            }
        }

        // Backward compatibility, no exceptional code paths were lost
        require(ioException > 0) { "At least one IOException expected" }
        require(arithmeticException > 0) { "At least one ArithmeticException expected" }
        require(aioobException > 0) { "At least one ArrayIndexOutOfBoundsException expected" }
    }

    private fun wrapperDispatcher(context: CoroutineContext): CoroutineContext {
        val dispatcher = context[ContinuationInterceptor] as CoroutineDispatcher
        return object : CoroutineDispatcher() {
            override fun dispatch(context: CoroutineContext, block: Runnable) {
                dispatcher.dispatch(context, block)
            }
        }
    }
}
