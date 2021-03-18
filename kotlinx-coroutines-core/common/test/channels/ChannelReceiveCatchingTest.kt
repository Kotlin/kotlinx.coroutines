/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.test.*

class ChannelReceiveCatchingTest : TestBase() {
    @Test
    fun testChannelOfThrowables() = runTest {
        val channel = Channel<Throwable>()
        launch {
            channel.send(TestException1())
            channel.close(TestException2())
        }

        val element = channel.receiveCatching()
        assertTrue(element.getOrThrow() is TestException1)
        assertTrue(element.getOrNull() is TestException1)

        val closed = channel.receiveCatching()
        assertTrue(closed.isClosed)
        assertTrue(closed.isFailure)
        assertTrue(closed.exceptionOrNull() is TestException2)
    }

    @Test
    @Suppress("ReplaceAssertBooleanWithAssertEquality") // inline classes test
    fun testNullableIntChanel() = runTest {
        val channel = Channel<Int?>()
        launch {
            expect(2)
            channel.send(1)
            expect(3)
            channel.send(null)

            expect(6)
            channel.close()
        }

        expect(1)
        val element = channel.receiveCatching()
        assertEquals(1, element.getOrThrow())
        assertEquals(1, element.getOrNull())
        assertEquals("Value(1)", element.toString())
        assertTrue(ChannelResult.value(1) == element) // Don't box
        assertFalse(element.isFailure)
        assertFalse(element.isClosed)

        expect(4)
        val nullElement = channel.receiveCatching()
        assertNull(nullElement.getOrThrow())
        assertNull(nullElement.getOrNull())
        assertEquals("Value(null)", nullElement.toString())
        assertTrue(ChannelResult.value(null) == nullElement) // Don't box
        assertFalse(element.isFailure)
        assertFalse(element.isClosed)

        expect(5)
        val closed = channel.receiveCatching()
        assertTrue(closed.isClosed)
        assertTrue(closed.isFailure)

        val closed2 = channel.receiveCatching()
        assertTrue(closed2.isClosed)
        assertTrue(closed.isFailure)
        assertNull(closed2.exceptionOrNull())
        finish(7)
    }

    @Test
    @ExperimentalUnsignedTypes
    fun testUIntChannel() = runTest {
        val channel = Channel<UInt>()
        launch {
            expect(2)
            channel.send(1u)
            yield()
            expect(4)
            channel.send((Long.MAX_VALUE - 1).toUInt())
            expect(5)
        }

        expect(1)
        val element = channel.receiveCatching()
        assertEquals(1u, element.getOrThrow())

        expect(3)
        val element2 = channel.receiveCatching()
        assertEquals((Long.MAX_VALUE - 1).toUInt(), element2.getOrThrow())
        finish(6)
    }

    @Test
    fun testCancelChannel() = runTest {
        val channel = Channel<Boolean>()
        launch {
            expect(2)
            channel.cancel()
        }

        expect(1)
        val closed = channel.receiveCatching()
        assertTrue(closed.isClosed)
        assertTrue(closed.isFailure)
        finish(3)
    }

    @Test
    @ExperimentalUnsignedTypes
    fun testReceiveResultChannel() = runTest {
        val channel = Channel<ChannelResult<UInt>>()
        launch {
            channel.send(ChannelResult.value(1u))
            channel.send(ChannelResult.closed(TestException1()))
            channel.close(TestException2())
        }

        val intResult = channel.receiveCatching()
        assertEquals(1u, intResult.getOrThrow().getOrThrow())
        assertFalse(intResult.isFailure)
        assertFalse(intResult.isClosed)

        val closeCauseResult = channel.receiveCatching()
        assertTrue(closeCauseResult.getOrThrow().exceptionOrNull() is TestException1)

        val closeCause = channel.receiveCatching()
        assertTrue(closeCause.isClosed)
        assertTrue(closeCause.isFailure)
        assertTrue(closeCause.exceptionOrNull() is TestException2)
    }

    @Test
    fun testToString() = runTest {
        val channel = Channel<String>(1)
        channel.send("message")
        channel.close(TestException1("OK"))
        assertEquals("Value(message)", channel.receiveCatching().toString())
        // toString implementation for exception differs on every platform
        val str = channel.receiveCatching().toString()
        if (!str.matches("Closed\\(.*TestException1: OK\\)".toRegex()))
            error("Unexpected string: '$str'")
    }
}
