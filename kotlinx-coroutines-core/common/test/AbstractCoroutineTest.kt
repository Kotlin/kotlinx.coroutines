/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.test.*

@Suppress("DEPRECATION") // cancel(cause)
class AbstractCoroutineTest : TestBase() {
    @Test
    fun testNotifications() = runTest {
        expect(1)
        val coroutineContext = coroutineContext // workaround for KT-22984
        val coroutine = object : AbstractCoroutine<String>(coroutineContext, false) {
            override fun onStart() {
                expect(3)
            }

            override fun onCancellation(cause: Throwable?) {
                assertEquals(null, cause)
                expect(5)
            }

            override fun onCompleted(value: String) {
                assertEquals("OK", value)
                expect(8)
            }

            override fun onCompletedExceptionally(exception: Throwable) {
                expectUnreached()
            }
        }

        coroutine.invokeOnCompletion(onCancelling = true) {
            assertEquals(null, it)
            expect(6)
        }

        coroutine.invokeOnCompletion {
            assertEquals(null, it)
            expect(7)
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
        val coroutine = object : AbstractCoroutine<String>(coroutineContext + NonCancellable, false) {
            override fun onStart() {
                expect(3)
            }

            override fun onCancellation(cause: Throwable?) {
                assertTrue(cause is TestException1)
                expect(5)
            }

            override fun onCompleted(value: String) {
                expectUnreached()
            }

            override fun onCompletedExceptionally(exception: Throwable) {
                assertTrue(exception is TestException1)
                expect(9)
            }
        }

        coroutine.invokeOnCompletion(onCancelling = true) {
            assertTrue(it is TestException1)
            expect(6)
        }

        coroutine.invokeOnCompletion {
            assertTrue(it is TestException1)
            expect(8)
        }

        expect(2)
        coroutine.start()
        expect(4)
        coroutine.cancel(TestException1())
        expect(7)
        coroutine.resumeWithException(TestException2())
        finish(10)
    }
}