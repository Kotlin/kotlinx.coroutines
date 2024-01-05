package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.coroutines.*
import kotlin.test.*

@Suppress("DEPRECATION") // cancel(cause)
class AbstractCoroutineTest : TestBase() {
    @Test
    fun testNotifications() = runTest {
        expect(1)
        val coroutineContext = coroutineContext // workaround for KT-22984
        val coroutine = object : AbstractCoroutine<String>(coroutineContext, true, false) {
            override fun onStart() {
                expect(3)
            }

            override fun onCancelling(cause: Throwable?) {
                assertNull(cause)
                expect(5)
            }

            override fun onCompleted(value: String) {
                assertEquals("OK", value)
                expect(6)
            }

            override fun onCancelled(cause: Throwable, handled: Boolean) {
                expectUnreached()
            }
        }

        coroutine.invokeOnCompletion(onCancelling = true) {
            assertNull(it)
            expect(7)
        }

        coroutine.invokeOnCompletion {
            assertNull(it)
            expect(8)
        }
        expect(2)
        coroutine.start()
        expect(4)
        coroutine.resume("OK")
        finish(9)
    }

    @Test
    fun testNotificationsWithException() = runTest {
        expect(1)
        val coroutineContext = coroutineContext // workaround for KT-22984
        val coroutine = object : AbstractCoroutine<String>(coroutineContext + NonCancellable, true, false) {
            override fun onStart() {
                expect(3)
            }

            override fun onCancelling(cause: Throwable?) {
                assertIs<TestException1>(cause)
                expect(5)
            }

            override fun onCompleted(value: String) {
                expectUnreached()
            }

            override fun onCancelled(cause: Throwable, handled: Boolean) {
                assertIs<TestException1>(cause)
                expect(8)
            }
        }

        coroutine.invokeOnCompletion(onCancelling = true) {
            assertIs<TestException1>(it)
            expect(6)
        }

        coroutine.invokeOnCompletion {
            assertIs<TestException1>(it)
            expect(9)
        }

        expect(2)
        coroutine.start()
        expect(4)
        coroutine.cancelCoroutine(TestException1())
        expect(7)
        coroutine.resumeWithException(TestException2())
        finish(10)
    }
}
