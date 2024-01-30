package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.coroutines.*
import kotlin.test.*

class DelayExceptionTest : TestBase() {

    @Test
    fun testMaxDelay() = runBlocking {
        expect(1)
        val job = launch {
            expect(2)
            delay(Long.MAX_VALUE)
        }
        yield()
        job.cancel()
        finish(3)
    }
}
