/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.selects

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.intrinsics.*
import kotlin.test.*

class SelectArrayChannelTest : TestBase() {

    @Test
    fun testSelectSendSuccess() = runTest {
        expect(1)
        val channel = Channel<String>(1)
        launch {
            expect(2)
            assertEquals("OK", channel.receive())
            finish(6)
        }
        yield() // to launched coroutine
        expect(3)
        select<Unit> {
            channel.onSend("OK") {
                expect(4)
            }
        }
        expect(5)
    }

    @Test
    fun testSelectSendSuccessWithDefault() = runTest {
        expect(1)
        val channel = Channel<String>(1)
        launch {
            expect(2)
            assertEquals("OK", channel.receive())
            finish(6)
        }
        yield() // to launched coroutine
        expect(3)
        select<Unit> {
            channel.onSend("OK") {
                expect(4)
            }
            default {
                expectUnreached()
            }
        }
        expect(5)
    }

    @Test
    fun testSelectSendReceiveBuf() = runTest {
        expect(1)
        val channel = Channel<String>(1)
        select<Unit> {
            channel.onSend("OK") {
                expect(2)
            }
        }
        expect(3)
        select<Unit> {
            channel.onReceive { v ->
                expect(4)
                assertEquals("OK", v)
            }
        }
        finish(5)
    }

    @Test
    fun testSelectSendWait() = runTest {
        expect(1)
        val channel = Channel<String>(1)
        launch {
            expect(4)
            assertEquals("BUF", channel.receive())
            expect(5)
            assertEquals("OK", channel.receive())
            expect(6)
        }
        expect(2)
        channel.send("BUF")
        expect(3)
        select<Unit> {
            channel.onSend("OK") {
                expect(7)
            }
        }
        finish(8)
    }

    @Test
    fun testSelectReceiveSuccess() = runTest {
        expect(1)
        val channel = Channel<String>(1)
        channel.send("OK")
        expect(2)
        select<Unit> {
            channel.onReceive { v ->
                expect(3)
                assertEquals("OK", v)
            }
        }
        finish(4)
    }

    @Test
    fun testSelectReceiveSuccessWithDefault() = runTest {
        expect(1)
        val channel = Channel<String>(1)
        channel.send("OK")
        expect(2)
        select<Unit> {
            channel.onReceive { v ->
                expect(3)
                assertEquals("OK", v)
            }
            default {
                expectUnreached()
            }
        }
        finish(4)
    }

    @Test
    fun testSelectReceiveWaitWithDefault() = runTest {
        expect(1)
        val channel = Channel<String>(1)
        select<Unit> {
            channel.onReceive {
                expectUnreached()
            }
            default {
                expect(2)
            }
        }
        expect(3)
        channel.send("BUF")
        expect(4)
        // make sure second send blocks (select above is over)
        launch {
            expect(6)
            channel.send("CHK")
            finish(10)
        }
        expect(5)
        yield()
        expect(7)
        assertEquals("BUF", channel.receive())
        expect(8)
        assertEquals("CHK", channel.receive())
        expect(9)
    }

    @Test
    fun testSelectReceiveWait() = runTest {
        expect(1)
        val channel = Channel<String>(1)
        launch {
            expect(3)
            channel.send("OK")
            expect(4)
        }
        expect(2)
        select<Unit> {
            channel.onReceive { v ->
                expect(5)
                assertEquals("OK", v)
            }
        }
        finish(6)
    }

    @Test
    fun testSelectReceiveClosed() = runTest({it is ClosedReceiveChannelException}) {
        expect(1)
        val channel = Channel<String>(1)
        channel.close()
        finish(2)
        select<Unit> {
            channel.onReceive {
                expectUnreached()
            }
        }
        expectUnreached()
    }

    @Test
    fun testSelectReceiveWaitClosed() = runTest({it is ClosedReceiveChannelException}) {
        expect(1)
        val channel = Channel<String>(1)
        launch {
            expect(3)
            channel.close()
            finish(4)
        }
        expect(2)
        select<Unit> {
            channel.onReceive {
                expectUnreached()
            }
        }
        expectUnreached()
    }

    @Test
    fun testSelectSendResourceCleanup() = runTest {
        val channel = Channel<Int>(1)
        val n = 1000
        expect(1)
        channel.send(-1) // fill the buffer, so all subsequent sends cannot proceed
        repeat(n) { i ->
            select {
                channel.onSend(i) { expectUnreached() }
                default { expect(i + 2) }
            }
        }
        finish(n + 2)
    }

    @Test
    fun testSelectReceiveResourceCleanup() = runTest {
        val channel = Channel<Int>(1)
        val n = 1000
        expect(1)
        repeat(n) { i ->
            select {
                channel.onReceive { expectUnreached() }
                default { expect(i + 2) }
            }
        }
        finish(n + 2)
    }

    @Test
    fun testSelectReceiveDispatchNonSuspending() = runTest {
        val channel = Channel<Int>(1)
        expect(1)
        channel.send(42)
        expect(2)
        launch {
            expect(4)
            select<Unit> {
                channel.onReceive { v ->
                    expect(5)
                    assertEquals(42, v)
                    expect(6)
                }
            }
            expect(7) // returns from select without further dispatch
        }
        expect(3)
        yield() // to launched
        finish(8)
    }

    @Test
    fun testSelectReceiveDispatchNonSuspending2() = runTest {
        val channel = Channel<Int>(1)
        expect(1)
        channel.send(42)
        expect(2)
        launch {
            expect(4)
            select<Unit> {
                channel.onReceive { v ->
                    expect(5)
                    assertEquals(42, v)
                    expect(6)
                    yield() // back to main
                    expect(8)
                }
            }
            expect(9) // returns from select without further dispatch
        }
        expect(3)
        yield() // to launched
        expect(7)
        yield() // again
        finish(10)
    }

    @Test
    fun testSelectReceiveOrClosedWaitClosed() = runTest {
        expect(1)
        val channel = Channel<String>(1)
        launch {
            expect(3)
            channel.close()
            expect(4)
        }
        expect(2)
        select<Unit> {
            channel.onReceiveCatching {
                expect(5)
                assertTrue(it.isClosed)
                assertNull(it.exceptionOrNull())
            }
        }

        finish(6)
    }

    @Test
    fun testSelectReceiveOrClosedWaitClosedWithCause() = runTest {
        expect(1)
        val channel = Channel<String>(1)
        launch {
            expect(3)
            channel.close(TestException())
            expect(4)
        }
        expect(2)
        select<Unit> {
            channel.onReceiveCatching {
                expect(5)
                assertTrue(it.isClosed)
                assertTrue(it.exceptionOrNull() is TestException)
            }
        }

        finish(6)
    }

    @Test
    fun testSelectReceiveCatching() = runTest {
        val c = Channel<Int>(1)
        val iterations = 10
        expect(1)
        val job = launch {
            repeat(iterations) {
                select<Unit> {
                    c.onReceiveCatching { v ->
                        expect(4 + it * 2)
                        assertEquals(it, v.getOrNull())
                    }
                }
            }
        }

        expect(2)
        repeat(iterations) {
            expect(3 + it * 2)
            c.send(it)
            yield()
        }

        job.join()
        finish(3 + iterations * 2)
    }

    @Test
    fun testSelectReceiveOrClosedDispatch() = runTest {
        val c = Channel<Int>(1)
        expect(1)
        launch {
            expect(3)
            val res = select<String> {
                c.onReceiveCatching { v ->
                    expect(6)
                    assertEquals(42, v.getOrNull())
                    yield() // back to main
                    expect(8)
                    "OK"
                }
            }
            expect(9)
            assertEquals("OK", res)
        }
        expect(2)
        yield() // to launch
        expect(4)
        c.send(42) // do not suspend
        expect(5)
        yield() // to receive
        expect(7)
        yield() // again
        finish(10)
    }

    // only for debugging
    internal fun <R> SelectBuilder<R>.default(block: suspend () -> R) {
        this as SelectBuilderImpl // type assertion
        if (!trySelect()) return
        block.startCoroutineUnintercepted(this)
    }

    @Test
    fun testSelectReceiveOrClosedForClosedChannel() = runTest {
        val channel = Channel<Int>(1)
        channel.close()
        expect(1)
        select<Unit> {
            expect(2)
            channel.onReceiveCatching {
                assertTrue(it.isClosed)
                assertNull(it.exceptionOrNull())
                finish(3)
            }
        }
    }

    @Test
    fun testSelectReceiveOrClosedForClosedChannelWithValue() = runTest {
        val channel = Channel<Int>(1)
        channel.send(42)
        channel.close()
        expect(1)
        select<Unit> {
            expect(2)
            channel.onReceiveCatching {
                assertFalse(it.isClosed)
                assertEquals(42, it.getOrNull())
                finish(3)
            }
        }
    }
}
