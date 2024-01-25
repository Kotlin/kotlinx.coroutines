package kotlinx.coroutines.debug.junit5

import kotlinx.coroutines.*
import org.junit.jupiter.api.*
import org.junit.jupiter.api.extension.*

class RegisterExtensionExample {
    @JvmField
    @RegisterExtension
    internal val timeout = CoroutinesTimeoutExtension.seconds(5)

    @Test
    fun testThatHangs() = runBlocking {
        delay(Long.MAX_VALUE) // somewhere deep in the stack
    }
}