package kotlinx.coroutines.exceptions

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.testing.exceptions.*
import java.io.*
import kotlin.coroutines.*
import kotlin.test.*

@Suppress("DEPRECATION")
class SuppressionTests : TestBase() {
    @Test
    fun testNotificationsWithException() = runTest {
        expect(1)
        val coroutineContext = kotlin.coroutines.coroutineContext + NonCancellable // workaround for KT-22984
        val coroutine = object : AbstractCoroutine<String>(coroutineContext, true, false) {
            override fun onStart() {
                expect(3)
            }

            override fun onCancelling(cause: Throwable?) {
                assertIs<ArithmeticException>(cause)
                assertTrue(cause.suppressed.isEmpty())
                expect(5)
            }

            override fun onCompleted(value: String) {
                expectUnreached()
            }

            override fun onCancelled(cause: Throwable, handled: Boolean) {
                assertIs<ArithmeticException>(cause)
                checkException<IOException>(cause.suppressed[0])
                expect(8)
            }
        }

        coroutine.invokeOnCompletion(onCancelling = true) {
            assertIs<ArithmeticException>(it)
            assertTrue(it.suppressed.isEmpty())
            expect(6)
        }

        coroutine.invokeOnCompletion {
            assertIs<ArithmeticException>(it)
            checkException<IOException>(it.suppressed[0])
            expect(9)
        }

        expect(2)
        coroutine.start()
        expect(4)
        coroutine.cancelInternal(ArithmeticException())
        expect(7)
        coroutine.resumeWithException(IOException())
        finish(10)
    }

    @Test
    fun testExceptionUnwrapping() = runTest {
        val channel = Channel<Int>()

        val deferred = async(NonCancellable) {
            launch {
                while (true) channel.send(1)
            }

            launch {
                val exception = RecoverableTestCancellationException()
                channel.cancel(exception)
                throw exception
            }
        }

        try {
            deferred.await()
        } catch (e: RecoverableTestException) {
            assertTrue(e.suppressed.isEmpty())
            assertTrue(e.cause!!.suppressed.isEmpty())
        }
    }
}
