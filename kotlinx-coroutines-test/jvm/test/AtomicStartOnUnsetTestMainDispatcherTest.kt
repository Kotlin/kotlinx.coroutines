package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.testing.*
import org.junit.*
import org.junit.Test
import org.junit.rules.*
import kotlin.test.*

class AtomicStartOnUnsetTestMainDispatcherTest : OrderedExecutionTestBase() {

    @Rule
    @JvmField
    val timeout: Timeout = Timeout.seconds(5)

    @Test
    fun testAtomicStartOnUnsetTestMainDispatcherFailsFast() {
        Dispatchers.resetMain()

        try {
            val exception = assertFailsWith<IllegalStateException> {
                runBlocking<Unit> {
                    launch(
                        Dispatchers.Main,
                        start = CoroutineStart.ATOMIC,
                    ) {}
                }
            }

            assertTrue(
                exception.message.orEmpty().contains(
                    "the test dispatcher was unset"
                ),
                "Unexpected exception: $exception",
            )
        } finally {
            Dispatchers.resetMain()
        }
    }
}
