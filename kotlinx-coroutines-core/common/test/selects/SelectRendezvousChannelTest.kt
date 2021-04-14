/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines.selects

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.intrinsics.*
import kotlin.test.*

class SelectRendezvousChannelTest : TestBase() {

    @Test
    fun testSelectSendSuccess() = runTest {
        expect(1)
        val channel = Channel<String>(Channel.RENDEZVOUS)
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
        val channel = Channel<String>(Channel.RENDEZVOUS)
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
    fun testSelectSendWaitWithDefault() = runTest {
        expect(1)
        val channel = Channel<String>(Channel.RENDEZVOUS)
        select<Unit> {
            channel.onSend("OK") {
                expectUnreached()
            }
            default {
                expect(2)
            }
        }
        expect(3)
        // make sure receive blocks (select above is over)
        launch {
            expect(5)
            assertEquals("CHK", channel.receive())
            finish(8)
        }
        expect(4)
        yield()
        expect(6)
        channel.send("CHK")
        expect(7)
    }

    @Test
    fun testSelectSendWait() = runTest {
        expect(1)
        val channel = Channel<String>(Channel.RENDEZVOUS)
        launch {
            expect(3)
            assertEquals("OK", channel.receive())
            expect(4)
        }
        expect(2)
        select<Unit> {
            channel.onSend("OK") {
                expect(5)
            }
        }
        finish(6)
    }

    @Test
    fun testSelectReceiveSuccess() = runTest {
        expect(1)
        val channel = Channel<String>(Channel.RENDEZVOUS)
        launch {
            expect(2)
            channel.send("OK")
            finish(6)
        }
        yield() // to launched coroutine
        expect(3)
        select<Unit> {
            channel.onReceive { v ->
                expect(4)
                assertEquals("OK", v)
            }
        }
        expect(5)
    }

    @Test
    fun testSelectReceiveSuccessWithDefault() = runTest {
        expect(1)
        val channel = Channel<String>(Channel.RENDEZVOUS)
        launch {
            expect(2)
            channel.send("OK")
            finish(6)
        }
        yield() // to launched coroutine
        expect(3)
        select<Unit> {
            channel.onReceive { v ->
                expect(4)
                assertEquals("OK", v)
            }
            default {
                expectUnreached()
            }
        }
        expect(5)
    }

    @Test
    fun testSelectReceiveWaitWithDefault() = runTest {
        expect(1)
        val channel = Channel<String>(Channel.RENDEZVOUS)
        select<Unit> {
            channel.onReceive {
                expectUnreached()
            }
            default {
                expect(2)
            }
        }
        expect(3)
        // make sure send blocks (select above is over)
        launch {
            expect(5)
            channel.send("CHK")
            finish(8)
        }
        expect(4)
        yield()
        expect(6)
        assertEquals("CHK", channel.receive())
        expect(7)
    }

    @Test
    fun testSelectReceiveWait() = runTest {
        expect(1)
        val channel = Channel<String>(Channel.RENDEZVOUS)
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
    fun testSelectReceiveClosed() = runTest(expected = { it is ClosedReceiveChannelException }) {
        expect(1)
        val channel = Channel<String>(Channel.RENDEZVOUS)
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
    fun testSelectReceiveWaitClosed() = runTest(expected = {it is ClosedReceiveChannelException}) {
        expect(1)
        val channel = Channel<String>(Channel.RENDEZVOUS)
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
        val channel = Channel<Int>(Channel.RENDEZVOUS)
        val n = 1_000
        expect(1)
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
        val channel = Channel<Int>(Channel.RENDEZVOUS)
        val n = 1_000
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
    fun testSelectAtomicFailure() = runTest {
        val c1 = Channel<Int>(Channel.RENDEZVOUS)
        val c2 = Channel<Int>(Channel.RENDEZVOUS)
        expect(1)
        launch {
            expect(3)
            val res = select<String> {
                c1.onReceive { v1 ->
                    expect(4)
                    assertEquals(42, v1)
                    yield() // back to main
                    expect(7)
                    "OK"
                }
                c2.onReceive {
                    "FAIL"
                }
            }
            expect(8)
            assertEquals("OK", res)
        }
        expect(2)
        c1.send(42) // send to coroutine, suspends
        expect(5)
        c2.close() // makes sure that selected expression does not fail!
        expect(6)
        yield() // back
        finish(9)
    }

    @Test
    fun testSelectWaitDispatch() = runTest {
        val c = Channel<Int>(Channel.RENDEZVOUS)
        expect(1)
        launch {
            expect(3)
            val res = select<String> {
                c.onReceive { v ->
                    expect(6)
                    assertEquals(42, v)
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

    @Test
    fun testSelectReceiveCatchingWaitClosed() = runTest {
        expect(1)
        val channel = Channel<String>(Channel.RENDEZVOUS)
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
    fun testSelectReceiveCatchingWaitClosedWithCause() = runTest {
        expect(1)
        val channel = Channel<String>(Channel.RENDEZVOUS)
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
    fun testSelectReceiveCatchingForClosedChannel() = runTest {
        val channel = Channel<Unit>()
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
    fun testSelectReceiveCatching() = runTest {
        val channel = Channel<Int>(Channel.RENDEZVOUS)
        val iterations = 10
        expect(1)
        val job = launch {
            repeat(iterations) {
                select<Unit> {
                    channel.onReceiveCatching { v ->
                        expect(4 + it * 2)
                        assertEquals(it, v.getOrThrow())
                    }
                }
            }
        }

        expect(2)
        repeat(iterations) {
            expect(3 + it * 2)
            channel.send(it)
            yield()
        }

        job.join()
        finish(3 + iterations * 2)
    }

    @Test
    fun testSelectReceiveCatchingDispatch() = runTest {
        val c = Channel<Int>(Channel.RENDEZVOUS)
        expect(1)
        launch {
            expect(3)
            val res = select<String> {
                c.onReceiveCatching { v ->
                    expect(6)
                    assertEquals(42, v.getOrThrow())
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

    @Test
    fun testSelectSendWhenClosed() = runTest {
        expect(1)
        val c = Channel<Int>(Channel.RENDEZVOUS)
        val sender = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            c.send(1) // enqueue sender
            expectUnreached()
        }
        c.close() // then close
        assertFailsWith<ClosedSendChannelException> {
            // select sender should fail
            expect(3)
            select {
                c.onSend(2) {
                    expectUnreached()
                }
            }
        }
        sender.cancel()
        finish(4)
    }

    // only for debugging
    internal fun <R> SelectBuilder<R>.default(block: suspend () -> R) {
        this as SelectBuilderImpl // type assertion
        if (!trySelect()) return
        block.startCoroutineUnintercepted(this)
    }

    @Test
    fun testSelectSendAndReceive() = runTest {
        val c = Channel<Int>()
        assertFailsWith<IllegalStateException> {
            select<Unit> {
                c.onSend(1) { expectUnreached() }
                c.onReceive { expectUnreached() }
            }
        }
        checkNotBroken(c)
    }

    @Test
    fun testSelectReceiveAndSend() = runTest {
        val c = Channel<Int>()
        assertFailsWith<IllegalStateException> {
            select<Unit> {
                c.onReceive { expectUnreached() }
                c.onSend(1) { expectUnreached() }
            }
        }
        checkNotBroken(c)
    }

    // makes sure the channel is not broken
    private suspend fun checkNotBroken(c: Channel<Int>) {
        coroutineScope {
            launch {
                c.send(42)
            }
            assertEquals(42, c.receive())
        }
    }
}
