package kotlinx.coroutines.test

import kotlinx.coroutines.*
import org.junit.Rule
import org.junit.rules.Timeout
import kotlin.test.*

class UnsetMainFailFastTest {

    @get:Rule
    val timeout: Timeout = Timeout.seconds(10)

    @Test
    fun testAtomicLaunch() {
        assertFailsWith<IllegalStateException>("the test dispatcher was unset") {
            runBlocking<Unit> {
                launch(Dispatchers.Main, start = CoroutineStart.ATOMIC) { fail() }
            }
        }
    }
}
