package kotlinx.coroutines.testing

import kotlin.concurrent.thread
import kotlin.test.*

class CountDownLatchJvmTest {
    @Test
    fun testCountDownAndAwait() {
        val latch = CountDownLatch(1)
        latch.countDown()
        latch.await()
    }

    @Test
    fun testAwaitAndCountDown() {
        val latch = CountDownLatch(1)
        val t1 = thread {
            latch.await()
        }
        val t2 = thread {
            Thread.sleep(100)
            latch.countDown()
        }
        t1.join()
        t2.join()
    }
}
