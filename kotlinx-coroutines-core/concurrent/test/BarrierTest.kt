import kotlinx.coroutines.testing.*
import kotlinx.coroutines.testing.TestBase
import kotlin.test.Test

class BarrierTest : TestBase() {
    @Test
    fun testFoo() {
        val barrier = ConcurrentCyclicBarrier(5)
    }
}
