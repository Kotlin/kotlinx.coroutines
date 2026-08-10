package kotlinx.coroutines

import kotlin.test.*
import kotlinx.coroutines.testing.*
import kotlin.time.Duration.Companion.milliseconds

class DefaultDelayTest: TestBase() {
    @Test
    fun testDelayOnUnconfined() = runTest {
        val latch = CountDownLatch(1)
        launch(Dispatchers.Unconfined) {
            delay(1.milliseconds)
            latch.await()
        }
        delay(10.milliseconds)
        latch.countDown()
    }
}
