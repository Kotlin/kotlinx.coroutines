/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.test.*

class ChannelReceiveOrClosedTest : TestBase() {
    @Test
    fun testChannelOfThrowables() = runTest {
        val channel = Channel<Throwable>()
        launch {
            channel.send(TestException1())
            channel.close(TestException2())
        }

        val element = channel.receiveOrClosed()
        assertTrue(element.value is TestException1)
        assertTrue(element.valueOrNull is TestException1)

        val closed = channel.receiveOrClosed()
        assertTrue(closed.isClosed)
        assertTrue(closed.closeCause is TestException2)
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
        val element = channel.receiveOrClosed()
        assertEquals(1, element.value)
        assertEquals(1, element.valueOrNull)
        assertEquals("Value(1)", element.toString())
        assertTrue(ValueOrClosed.value(1) == element) // Don't box

        expect(4)
        val nullElement = channel.receiveOrClosed()
        assertNull(nullElement.value)
        assertNull(nullElement.valueOrNull)
        assertEquals("Value(null)", nullElement.toString())
        assertTrue(ValueOrClosed.value(null) == nullElement) // Don't box

        expect(5)
        val closed = channel.receiveOrClosed()
        assertTrue(closed.isClosed)

        val closed2 = channel.receiveOrClosed()
        assertTrue(closed2.isClosed)
        assertNull(closed2.closeCause)
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
        val element = channel.receiveOrClosed()
        assertEquals(1u, element.value)

        expect(3)
        val element2 = channel.receiveOrClosed()
        assertEquals((Long.MAX_VALUE - 1).toUInt(), element2.value)
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
        val closed = channel.receiveOrClosed()
        assertTrue(closed.isClosed)
        finish(3)
    }

    @Test
    @ExperimentalUnsignedTypes
    fun testReceiveResultChannel() = runTest {
        val channel = Channel<ValueOrClosed<UInt>>()
        launch {
            channel.send(ValueOrClosed.value(1u))
            channel.send(ValueOrClosed.closed(TestException1()))
            channel.close(TestException2())
        }

        val intResult = channel.receiveOrClosed()
        assertEquals(1u, intResult.value.value)

        val closeCauseResult = channel.receiveOrClosed()
        assertTrue(closeCauseResult.value.closeCause is TestException1)

        val closeCause = channel.receiveOrClosed()
        assertTrue(closeCause.isClosed)
        assertTrue(closeCause.closeCause is TestException2)
    }

    @Test
    fun testToString() = runTest {
        val channel = Channel<String>(1)
        channel.send("message")
        channel.close(TestException1())
        assertEquals("Value(message)", channel.receiveOrClosed().toString())
        // toString implementation for exception differs on every platform
        val str = channel.receiveOrClosed().toString()
        assertTrue(str.matches("Closed\\(.*TestException1\\)".toRegex()))
    }
}
