package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.test.*

class PromiseTest {
    @OptIn(ExperimentalWasmJsInterop::class)
    @Test
    fun testCompletionFromPromise() = runTest {
        var promiseEntered = false
        val p = promise {
            delay(1)
            promiseEntered = true
            null
        }
        delay(2)
        p.await()
        assertTrue(promiseEntered)
    }
}