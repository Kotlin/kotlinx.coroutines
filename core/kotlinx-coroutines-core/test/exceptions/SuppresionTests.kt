/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.exceptions

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.exceptions.*
import kotlinx.coroutines.experimental.selects.*
import java.io.*
import kotlin.test.*

/*
 * Set of counterparts to common tests which check suppressed exceptions
 */
class SuppresionTests : TestBase() {

    @Test
    fun testCancellationTransparency() = runTest {
        val deferred = async(kotlin.coroutines.experimental.coroutineContext, CoroutineStart.ATOMIC) {
            expect(2)
            throw ArithmeticException()
        }

        expect(1)
        deferred.cancel(IOException())

        try {
            deferred.await()
        } catch (e: IOException) {
            checkException<ArithmeticException>(e.suppressed()[0])
            finish(3)
        }
    }

    @Test
    fun testNotificationsWithException() = runTest {
        expect(1)
        val coroutineContext = kotlin.coroutines.experimental.coroutineContext // workaround for KT-22984
        val coroutine = object : AbstractCoroutine<String>(coroutineContext, false) {
            override fun onStart() {
                expect(3)
            }

            override fun onCancellation(cause: Throwable?) {
                assertTrue(cause is ArithmeticException)
                assertTrue(cause!!.suppressed().isEmpty())
                expect(5)
            }

            override fun onCompleted(value: String) {
                expectUnreached()
            }

            override fun onCompletedExceptionally(exception: Throwable) {
                assertTrue(exception is ArithmeticException)
                checkException<IOException>(exception.suppressed()[0])
                expect(9)
            }
        }

        coroutine.invokeOnCompletion(onCancelling = true) {
            assertTrue(it is ArithmeticException)
            assertTrue(it!!.suppressed().isEmpty())
            expect(6)
        }

        coroutine.invokeOnCompletion {
            assertTrue(it is ArithmeticException)
            checkException<IOException>(it!!.suppressed()[0])
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
}