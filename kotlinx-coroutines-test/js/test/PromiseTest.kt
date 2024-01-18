package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.test.*

class PromiseTest {
    @Test
    fun testCompletionFromPromise() = runTest {
        var promiseEntered = false
        val p = promise {
            delay(1)
            promiseEntered = true
        }
        delay(2)
        p.await()
        assertTrue(promiseEntered)
    }
}