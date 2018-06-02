
@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.timeunit.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

class DelayTest : TestBase() {

    @Test
    fun testCancellation() = runTest(expected = {it is JobCancellationException}) {
        runAndCancel(3600, TimeUnit.SECONDS)
    }

    @Test
    fun testMaxLongValue()= runTest(expected = {it is JobCancellationException}) {
        runAndCancel(Long.MAX_VALUE)
    }

    @Test
    fun testMaxIntValue()= runTest(expected = {it is JobCancellationException}) {
        runAndCancel(Int.MAX_VALUE.toLong())
    }

    @Test
    fun testOverflowOnUnitConversion()= runTest(expected = {it is JobCancellationException}) {
        runAndCancel(Long.MAX_VALUE, TimeUnit.SECONDS)
    }

    @Test
    fun testRegularDelay() = runTest {
        val deferred = async(coroutineContext) {
            expect(2)
            delay(1)
            expect(3)
        }

        expect(1)
        yield()
        deferred.await()
        finish(4)
    }

    private suspend fun runAndCancel(time: Long, unit: TimeUnit = TimeUnit.MILLISECONDS) {
        expect(1)
        val deferred = async(coroutineContext) {
            expect(2)
            delay(time, unit)
            expectUnreached()
        }

        yield()
        expect(3)
        require(deferred.isActive)
        deferred.cancel()
        finish(4)
        deferred.await()
    }
}
