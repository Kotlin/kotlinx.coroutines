package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import org.junit.*
import kotlin.test.Test
import kotlin.test.assertTrue
import kotlin.time.Duration.Companion.milliseconds

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

internal actual fun runningOnIoThread(): Boolean = Thread.currentThread().isIoDispatcherThread()
