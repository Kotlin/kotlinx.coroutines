package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.coroutines.*
import kotlin.test.*

/**
 * Regression test for https://github.com/Kotlin/kotlinx.coroutines/issues/4698.
 *
 * An exception during atomic coroutine dispatch must be reported
 * instead of leaving the parent waiting for a coroutine that never started.
 */
class CoroutineStartAtomicTest : TestBase() {

    private val brokenDispatcher = object : CoroutineDispatcher() {
        override fun dispatch(
            context: CoroutineContext,
            block: Runnable,
        ) = TODO("dispatcher is broken")
    }

    @Test
    fun testAtomicStartOnBrokenDispatcherFailsFast() = runTest {
        assertFailsWith<NotImplementedError> {
            assertCoroutineHangs {
                coroutineScope {
                    val job = launch(
                        brokenDispatcher,
                        start = CoroutineStart.ATOMIC,
                    ) {}

                    job.join()
                }
            }
        }
    }
}
