package kotlinx.coroutines

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

