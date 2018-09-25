/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.exceptions

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import org.junit.Test
import kotlin.test.*

class ProduceExceptionsTest : TestBase() {

    @Test
    fun testFailingProduce() = runTest(unhandled = listOf({ e -> e is TestException })) {
        expect(1)
        val producer = produce<Int>(Job()) {
            expect(2)
            try {
                yield()
            } finally {
                expect(3)
                throw TestException()

            }
        }

        yield()
        producer.cancel()
        yield()
        finish(4)
    }

    @Test
    fun testSuppressedExceptionUncaught() =
        runTest(unhandled = listOf({ e -> e is TestException && e.suppressed()[0] is TestException2 })) {
            val produce = produce<Int>(Job()) {
                launch(start = CoroutineStart.ATOMIC) {
                    throw TestException()
                }
                try {
                    delay(Long.MAX_VALUE)
                } finally {
                    throw TestException2()
                }
            }

            yield()
            produce.cancel()
        }

    @Test
    fun testSuppressedException() = runTest {
        val produce = produce<Int>(Job()) {
            launch(start = CoroutineStart.ATOMIC) {
                throw TestException()
            }
            try {
                delay(Long.MAX_VALUE)
            } finally {
                throw TestException2()
            }
        }

        try {
            produce.receive()
            expectUnreached()
        } catch (e: TestException) {
            assertTrue(e.suppressed()[0] is TestException2)
        }
    }

    class TestException : Exception()
    class TestException2 : Exception()
}
