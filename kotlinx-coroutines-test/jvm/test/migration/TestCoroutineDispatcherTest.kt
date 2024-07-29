package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.test.*

@Suppress("DEPRECATION", "DEPRECATION_ERROR")
class TestCoroutineDispatcherTest {

    @Test
    fun whenDispatcherResumed_doesAutoProgressCurrent() {
        val subject = TestCoroutineDispatcher()
        val scope = CoroutineScope(subject)
        var executed = 0
        scope.launch {
            executed++
        }

        assertEquals(1, executed)
    }

    @Test
    fun whenDispatcherResumed_doesNotAutoProgressTime() {
        val subject = TestCoroutineDispatcher()
        val scope = CoroutineScope(subject)
        var executed = 0
        scope.launch {
            delay(1_000)
            executed++
        }

        assertEquals(0, executed)
        subject.advanceUntilIdle()
        assertEquals(1, executed)
    }

}
