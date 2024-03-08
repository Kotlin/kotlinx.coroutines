import kotlinx.coroutines.*
import kotlinx.coroutines.test.*
import org.junit.Test
import kotlinx.coroutines.testing.*
import kotlin.test.*

@OptIn(ExperimentalCoroutinesApi::class)
internal class CooperativeCatchKtTest {

    @Test
    fun cooperativeCatchSuccess() = runTest {
        val result = cooperativeCatch { 42 }

        assertTrue(result.isSuccess)
        assertEquals(42, result.getOrNull())
    }

    @Test
    fun cooperativeCatchFailure() = runTest {
        val result = cooperativeCatch {
            error("exception thrown in cooperativeCatch")
            42
        }

        assertTrue(result.isFailure)
        assertNull(result.getOrNull())
    }

    @Test
    fun cooperativeCatchPropagatesCancellationException() = runTest(UnconfinedTestDispatcher()) {
        var cancellationExceptionWasPropagated = false
        val job = backgroundScope.launch {
            try {
                cooperativeCatch {
                    while (true) {
                        ensureActive()
                        delay(100)
                    }
                    42
                }
            } catch (e: CancellationException) {
                cancellationExceptionWasPropagated = true
                throw e
            }
        }

        job.cancel()

        assertTrue(cancellationExceptionWasPropagated)
    }

    @Test
    fun cooperativeMapAppliesTransform() = runTest {
        val result = cooperativeCatch {
            42
        }.cooperativeMap {
            "The answer to life, the universe, and everything? $it"
        }

        assertEquals("The answer to life, the universe, and everything? 42", result.getOrNull())
    }

    @Test
    fun cooperativeMapEncapsulatesThrowables() = runTest {
        val result = cooperativeCatch {
            42
        }.cooperativeMap {
            error("exception in cooperativeMap")
            "The answer to life, the universe, and everything? $it"
        }

        assertTrue(result.isFailure)
        assertNull(result.getOrNull())
    }

    @Test
    fun cooperativeMapPropagatesCancellationException() = runTest(UnconfinedTestDispatcher()) {
        var cancellationExceptionWasPropagated = false
        val job = backgroundScope.launch {
            try {
                cooperativeCatch {
                    42
                }.cooperativeMap {
                    while (true) {
                        ensureActive()
                        delay(100)
                    }
                }
            } catch (e: CancellationException) {
                cancellationExceptionWasPropagated = true
                throw e
            }
        }

        job.cancel()

        assertTrue(cancellationExceptionWasPropagated)
    }
}