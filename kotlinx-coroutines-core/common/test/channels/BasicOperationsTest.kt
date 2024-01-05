package kotlinx.coroutines.channels

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.test.*

class BasicOperationsTest : TestBase() {
    @Test
    fun testSimpleSendReceive() = runTest {
        // Parametrized common test :(
        TestChannelKind.values().forEach { kind -> testSendReceive(kind, 20) }
    }

    @Test
    fun testTrySendToFullChannel() = runTest {
        TestChannelKind.values().forEach { kind -> testTrySendToFullChannel(kind) }
    }

    @Test
    fun testTrySendAfterClose() = runTest {
        TestChannelKind.values().forEach { kind -> testTrySendAfterClose(kind) }
    }

    @Test
    fun testSendAfterClose() = runTest {
        TestChannelKind.values().forEach { kind -> testSendAfterClose(kind) }
    }

    @Test
    fun testReceiveCatching() = runTest {
        TestChannelKind.values().forEach { kind -> testReceiveCatching(kind) }
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
        channel.trySend(42)
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

    @Test
    fun testCancelledChannelInvokeOnClose() {
        val ch = Channel<Int>()
        ch.invokeOnClose { assertIs<CancellationException>(it) }
        ch.cancel()
    }

    @Test
    fun testCancelledChannelWithCauseInvokeOnClose() {
        val ch = Channel<Int>()
        ch.invokeOnClose { assertIs<TimeoutCancellationException>(it) }
        ch.cancel(TimeoutCancellationException(""))
    }

    @Test
    fun testThrowingInvokeOnClose() = runTest {
        val channel = Channel<Int>()
        channel.invokeOnClose {
            assertNull(it)
            expect(3)
            throw TestException()
        }

        launch {
            try {
                expect(2)
                channel.close()
            } catch (e: TestException) {
                expect(4)
            }
        }
        expect(1)
        yield()
        assertTrue(channel.isClosedForReceive)
        assertTrue(channel.isClosedForSend)
        assertFalse(channel.close())
        finish(5)
    }

    @Suppress("ReplaceAssertBooleanWithAssertEquality")
    private suspend fun testReceiveCatching(kind: TestChannelKind) = coroutineScope {
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
        assertTrue(ChannelResult.success(1) == result)

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

    private suspend fun testTrySendAfterClose(kind: TestChannelKind) = coroutineScope {
        val channel = kind.create<Int>()
        val d = async { channel.send(42) }
        yield()
        channel.close()

        assertTrue(channel.isClosedForSend)
        channel.trySend(2)
            .onSuccess { expectUnreached() }
            .onClosed {
                assertTrue { it is ClosedSendChannelException }
                if (!kind.isConflated) {
                    assertEquals(42, channel.receive())
                }
            }
        d.await()
    }

    private suspend fun testTrySendToFullChannel(kind: TestChannelKind) = coroutineScope {
        if (kind.isConflated || kind.capacity == Int.MAX_VALUE) return@coroutineScope
        val channel = kind.create<Int>()
        // Make it full
        repeat(11) {
            channel.trySend(42)
        }
        channel.trySend(1)
            .onSuccess { expectUnreached() }
            .onFailure { assertNull(it) }
            .onClosed {
                expectUnreached()
            }
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
