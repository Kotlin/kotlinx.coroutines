package kotlinx.coroutines.reactive

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.junit.*


class CancelledParentAttachTest : TestBase() {;

    @Test
    fun testFlow() = runTest {
        val f = flowOf(1, 2, 3).cancellable()
        val j = Job().also { it.cancel() }
        f.asPublisher(j).asFlow().collect()
    }

}
