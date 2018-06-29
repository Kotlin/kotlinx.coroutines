/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines.experimental.selects

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlinx.coroutines.experimental.intrinsics.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

class SelectRendezvousChannelTest : TestBase() {

    @Test
    fun testSelectSendSuccess() = runTest {
        expect(1)
        val channel = RendezvousChannel<String>()
        launch(coroutineContext) {
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
        val channel = RendezvousChannel<String>()
        launch(coroutineContext) {
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
        val channel = RendezvousChannel<String>()
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
        launch(coroutineContext) {
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
        val channel = RendezvousChannel<String>()
        launch(coroutineContext) {
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
        val channel = RendezvousChannel<String>()
        launch(coroutineContext) {
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
        val channel = RendezvousChannel<String>()
        launch(coroutineContext) {
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
        val channel = RendezvousChannel<String>()
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
        launch(coroutineContext) {
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
        val channel = RendezvousChannel<String>()
        launch(coroutineContext) {
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
        val channel = RendezvousChannel<String>()
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
        val channel = RendezvousChannel<String>()
        launch(coroutineContext) {
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
        val channel = RendezvousChannel<Int>()
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
        val channel = RendezvousChannel<Int>()
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
        val c1 = RendezvousChannel<Int>()
        val c2 = RendezvousChannel<Int>()
        expect(1)
        launch(coroutineContext) {
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
        val c = RendezvousChannel<Int>()
        expect(1)
        launch(coroutineContext) {
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

    // only for debugging
    internal fun <R> SelectBuilder<R>.default(block: suspend () -> R) {
        this as SelectBuilderImpl // type assertion
        if (!trySelect(null)) return
        block.startCoroutineUndispatched(this)
    }
}
