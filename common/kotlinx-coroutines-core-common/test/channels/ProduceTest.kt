/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

class ProduceTest : TestBase() {

    @Test
    fun testBasic() = runTest {
        val c = produce {
            expect(2)
            send(1)
            expect(3)
            send(2)
            expect(6)
        }
        expect(1)
        check(c.receive() == 1)
        expect(4)
        check(c.receive() == 2)
        expect(5)
        check(c.receiveOrNull() == null)
        finish(7)
    }

    @Test
    fun testCancelWithoutCause() = runTest {
        val c = produce {
            expect(2)
            send(1)
            expect(3)
            try {
                send(2) // will get cancelled
            } catch (e: Throwable) {
                finish(7)
                check(e is ClosedSendChannelException)
                throw e
            }
            expectUnreached()
        }
        expect(1)
        check(c.receive() == 1)
        expect(4)
        c.cancel()
        expect(5)
        assertNull(c.receiveOrNull())
        expect(6)
    }

    @Test
    fun testCancelWithCause() = runTest {
        val c = produce {
            expect(2)
            send(1)
            expect(3)
            try {
                send(2) // will get cancelled
            } catch (e: Exception) {
                finish(6)
                check(e is TestException)
                throw e
            }
            expectUnreached()
        }

        expect(1)
        check(c.receive() == 1)
        expect(4)
        c.cancel(TestException())

        try {
            assertNull(c.receiveOrNull())
            expectUnreached()
        } catch (e: TestException) {
            expect(5)
        }
    }

    @Test
    fun testCancelOnCompletionUnconfined() = runTest {
        cancelOnCompletion(Dispatchers.Unconfined)
    }

    @Test
    fun testCancelOnCompletion() = runTest {
        cancelOnCompletion(coroutineContext)
    }

    private suspend fun cancelOnCompletion(coroutineContext: CoroutineContext) = currentScope {
        val source = Channel<Int>()
        expect(1)
        val produced = produce<Int>(coroutineContext, onCompletion = source.consumes()) {
            expect(2)
            source.receive()
        }

        yield()
        expect(3)
        produced.cancel()
        try {
            source.receive()
            // TODO shouldn't it be ClosedReceiveChannelException ?
        } catch (e: CancellationException) {
            finish(4)
        }
    }

    private class TestException : Exception()
}
