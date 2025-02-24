package kotlinx.coroutines

import kotlin.test.*
import kotlinx.coroutines.testing.*

class DefaultDelayTest: TestBase() {
    @Test
    fun testDelayOnUnconfined() = runTest {
        val latch = CountDownLatch(1)
        launch(Dispatchers.Unconfined) {
            delay(1)
            latch.await()
        }
        delay(10)
        latch.countDown()
    }
}
