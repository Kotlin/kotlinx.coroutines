@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED", "DEPRECATION")

// KT-21913

package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.test.*
import kotlin.time.*
import kotlin.time.Duration.Companion.seconds
import kotlin.time.Duration.Companion.nanoseconds

class DelayDurationTest : TestBase() {

    @Test
    fun testCancellation() = runTest(expected = { it is CancellationException }) {
        runAndCancel(1.seconds)
    }

    @Test
    fun testInfinite() = runTest(expected = { it is CancellationException }) {
        runAndCancel(Duration.INFINITE)
    }

    @Test
    fun testRegularDelay() = runTest {
        val deferred = async {
            expect(2)
            delay(1.seconds)
            expect(4)
        }

        expect(1)
        yield()
        expect(3)
        deferred.await()
        finish(5)
    }

    @Test
    fun testNanoDelay() = runTest {
        val deferred = async {
            expect(2)
            delay(1.nanoseconds)
            expect(4)
        }

        expect(1)
        yield()
        expect(3)
        deferred.await()
        finish(5)
    }

    private suspend fun runAndCancel(time: Duration) = coroutineScope {
        expect(1)
        val deferred = async {
            expect(2)
            delay(time)
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
