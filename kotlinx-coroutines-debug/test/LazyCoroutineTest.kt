package kotlinx.coroutines.debug

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import org.junit.Test
import kotlin.test.*

class LazyCoroutineTest : DebugTestBase() {

    @Test
    fun testLazyCompletedCoroutine() = runTest {
        val job = launch(start = CoroutineStart.LAZY) {}
        job.invokeOnCompletion { expect(2) }
        expect(1)
        job.cancelAndJoin()
        expect(3)
        assertEquals(1, DebugProbes.dumpCoroutinesInfo().size) // Outer runBlocking
        verifyPartialDump(1, "BlockingCoroutine{Active}")
        finish(4)
    }
}
