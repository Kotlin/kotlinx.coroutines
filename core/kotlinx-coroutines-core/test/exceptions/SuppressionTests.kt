/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import java.io.*
import kotlin.coroutines.*
import kotlin.test.*

@Suppress("DEPRECATION")
class SuppressionTests : TestBase() {

    @Test
    fun testCancellationTransparency() = runTest {
        val deferred = async(NonCancellable, start = CoroutineStart.ATOMIC) {
            expect(2)
            throw ArithmeticException()
        }

        expect(1)
        deferred.cancel(TestException("Message"))

        try {
            deferred.await()
        } catch (e: TestException) {
            checkException<ArithmeticException>(e.suppressed[0])
            finish(3)
        }
    }

    @Test
    fun testNotificationsWithException() = runTest {
        expect(1)
        val coroutineContext = kotlin.coroutines.coroutineContext // workaround for KT-22984
        val coroutine = object : AbstractCoroutine<String>(coroutineContext, false) {
            override fun onStart() {
                expect(3)
            }

            override fun onCancellation(cause: Throwable?) {
                assertTrue(cause is ArithmeticException)
                assertTrue(cause.suppressed.isEmpty())
                expect(5)
            }

            override fun onCompleted(value: String) {
                expectUnreached()
            }

            override fun onCompletedExceptionally(exception: Throwable) {
                assertTrue(exception is ArithmeticException)
                checkException<IOException>(exception.suppressed[0])
                expect(9)
            }
        }

        coroutine.invokeOnCompletion(onCancelling = true) {
            assertTrue(it is ArithmeticException)
            assertTrue(it.suppressed.isEmpty())
            expect(6)
        }

        coroutine.invokeOnCompletion {
            assertTrue(it is ArithmeticException)
            checkException<IOException>(it.suppressed[0])
            expect(8)
        }

        expect(2)
        coroutine.start()
        expect(4)
        coroutine.cancel(ArithmeticException())
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
                val exception = RecoverableTestException()
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