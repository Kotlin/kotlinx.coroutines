/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.test.*

class BasicOperationsTest : TestBase() {
    @Test
    fun testSimpleSendReceive() = runTest {
        // Parametrized common test :(
        TestChannelKind.values().forEach { kind -> testSendReceive(kind, 20) }
    }

    @Test
    fun testOfferAfterClose() = runTest {
        TestChannelKind.values().forEach { kind -> testOffer(kind) }
    }

    @Test
    fun testSendAfterClose() = runTest {
        TestChannelKind.values().forEach { kind -> testSendAfterClose(kind) }
    }

    @Test
    fun testReceiveOrNullAfterClose() = runTest {
        TestChannelKind.values().forEach { kind -> testReceiveOrNull(kind) }
    }

    @Test
    fun testReceiveOrNullAfterCloseWithException() = runTest {
        TestChannelKind.values().forEach { kind -> testReceiveOrNullException(kind) }
    }

    @Test
    fun testReceiveCatching() = runTest {
        TestChannelKind.values().forEach { kind -> testReceiveOrClosed(kind) }
    }

    @Test
    fun testInvokeOnClose() = TestChannelKind.values().forEach { kind ->
        reset()
        val channel = kind.create<Int>()
        channel.invokeOnClose {
            if (it is AssertionError) {
                expect(3)
            }
        }
        expect(1)
        channel.offer(42)
        expect(2)
        channel.close(AssertionError())
        finish(4)
    }

    @Test
    fun testInvokeOnClosed() = TestChannelKind.values().forEach { kind ->
        reset()
        expect(1)
        val channel = kind.create<Int>()
        channel.close()
        channel.invokeOnClose { expect(2) }
        assertFailsWith<IllegalStateException> { channel.invokeOnClose { expect(3) } }
        finish(3)
    }

    @Test
    fun testMultipleInvokeOnClose() = TestChannelKind.values().forEach { kind ->
        reset()
        val channel = kind.create<Int>()
        channel.invokeOnClose { expect(3) }
        expect(1)
        assertFailsWith<IllegalStateException> { channel.invokeOnClose { expect(4) } }
        expect(2)
        channel.close()
        finish(4)
    }

    @Test
    fun testIterator() = runTest {
        TestChannelKind.values().forEach { kind ->
            val channel = kind.create<Int>()
            val iterator = channel.iterator()
            assertFailsWith<IllegalStateException> { iterator.next() }
            channel.close()
            assertFailsWith<IllegalStateException> { iterator.next() }
            assertFalse(iterator.hasNext())
        }
    }

    private suspend fun testReceiveOrNull(kind: TestChannelKind) = coroutineScope {
        val channel = kind.create<Int>()
        val d = async(NonCancellable) {
            channel.receive()
        }

        yield()
        channel.close()
        assertTrue(channel.isClosedForReceive)

        assertNull(channel.receiveOrNull())
        assertNull(channel.poll())

        d.join()
        assertTrue(d.getCancellationException().cause is ClosedReceiveChannelException)
    }

    private suspend fun testReceiveOrNullException(kind: TestChannelKind) = coroutineScope {
        val channel = kind.create<Int>()
        val d = async(NonCancellable) {
            channel.receive()
        }

        yield()
        channel.close(TestException())
        assertTrue(channel.isClosedForReceive)

        assertFailsWith<TestException> { channel.poll() }
        try {
            channel.receiveOrNull()
            fail()
        } catch (e: TestException) {
            // Expected
        }

        d.join()
        assertTrue(d.getCancellationException().cause is TestException)
    }

    @Suppress("ReplaceAssertBooleanWithAssertEquality")
    private suspend fun testReceiveOrClosed(kind: TestChannelKind) = coroutineScope {
        reset()
        val channel = kind.create<Int>()
        launch {
            expect(2)
            channel.send(1)
        }

        expect(1)
        val result = channel.receiveCatching()
        assertEquals(1, result.getOrThrow())
        assertEquals(1, result.getOrNull())
        assertTrue(ChannelResult.value(1) == result)

        expect(3)
        launch {
            expect(4)
            channel.close()
        }
        val closed = channel.receiveCatching()
        expect(5)
        assertNull(closed.getOrNull())
        assertTrue(closed.isClosed)
        assertNull(closed.exceptionOrNull())
        assertTrue(ChannelResult.closed<Int>(closed.exceptionOrNull()) == closed)
        finish(6)
    }

    private suspend fun testOffer(kind: TestChannelKind) = coroutineScope {
        val channel = kind.create<Int>()
        val d = async { channel.send(42) }
        yield()
        channel.close()

        assertTrue(channel.isClosedForSend)
        try {
            channel.offer(2)
            fail()
        } catch (e: ClosedSendChannelException) {
            if (!kind.isConflated) {
                assertEquals(42, channel.receive())
            }
        }

        d.await()
    }

    /**
     * [ClosedSendChannelException] should not be eaten.
     * See [https://github.com/Kotlin/kotlinx.coroutines/issues/957]
     */
    private suspend fun testSendAfterClose(kind: TestChannelKind) {
        assertFailsWith<ClosedSendChannelException> {
            coroutineScope {
                val channel = kind.create<Int>()
                channel.close()

                launch {
                    channel.send(1)
                }
            }
        }
    }

    private suspend fun testSendReceive(kind: TestChannelKind, iterations: Int) = coroutineScope {
        val channel = kind.create<Int>()
        launch {
            repeat(iterations) { channel.send(it) }
            channel.close()
        }
        var expected = 0
        for (x in channel) {
            if (!kind.isConflated) {
                assertEquals(expected++, x)
            } else {
                assertTrue(x >= expected)
                expected = x + 1
            }
        }
        if (!kind.isConflated) {
            assertEquals(iterations, expected)
        }
    }
}
