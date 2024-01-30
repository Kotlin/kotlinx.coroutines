package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import org.junit.*

class RunBlockingJvmTest : TestBase() {
    @Test
    fun testContract() {
        val rb: Int
        runBlocking {
            rb = 42
        }
        rb.hashCode() // unused
    }
}

