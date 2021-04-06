/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.test.*

class ConflatedBroadcastChannelTest : TestBase() {

    @Test
    fun testConcurrentModification() = runTest {
        val channel = ConflatedBroadcastChannel<Int>()
        val s1 = channel.openSubscription()
        val s2 = channel.openSubscription()

        val job1 = launch(Dispatchers.Unconfined, CoroutineStart.UNDISPATCHED) {
            expect(1)
            s1.receive()
            s1.cancel()
        }

        val job2 = launch(Dispatchers.Unconfined, CoroutineStart.UNDISPATCHED) {
            expect(2)
            s2.receive()
        }

        expect(3)
        channel.send(1)
        joinAll(job1, job2)
        finish(4)
    }

    @Test
    fun testBasicScenario() = runTest {
        expect(1)
        val broadcast = ConflatedBroadcastChannel<String>()
        assertTrue(exceptionFrom { broadcast.value } is IllegalStateException)
        assertNull(broadcast.valueOrNull)

        launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            val sub = broadcast.openSubscription()
            assertNull(sub.poll())
            expect(3)
            assertEquals("one", sub.receive()) // suspends
            expect(6)
            assertEquals("two", sub.receive()) // suspends
            expect(12)
            sub.cancel()
            expect(13)
        }

        expect(4)
        broadcast.send("one") // does not suspend
        assertEquals("one", broadcast.value)
        assertEquals("one", broadcast.valueOrNull)
        expect(5)
        yield() // to receiver
        expect(7)
        launch(start = CoroutineStart.UNDISPATCHED) {
            expect(8)
            val sub = broadcast.openSubscription()
            assertEquals("one", sub.receive()) // does not suspend
            expect(9)
            assertEquals("two", sub.receive()) // suspends
            expect(14)
            assertEquals("three", sub.receive()) // suspends
            expect(17)
            assertNull(sub.receiveCatching().getOrNull()) // suspends until closed
            expect(20)
            sub.cancel()
            expect(21)
        }

        expect(10)
        broadcast.send("two") // does not suspend
        assertEquals("two", broadcast.value)
        assertEquals("two", broadcast.valueOrNull)
        expect(11)
        yield() // to both receivers
        expect(15)
        broadcast.send("three") // does not suspend
        assertEquals("three", broadcast.value)
        assertEquals("three", broadcast.valueOrNull)
        expect(16)
        yield() // to second receiver
        expect(18)
        broadcast.close()
        assertTrue(exceptionFrom { broadcast.value } is IllegalStateException)
        assertNull(broadcast.valueOrNull)
        expect(19)
        yield() // to second receiver
        assertTrue(exceptionFrom { broadcast.send("four") } is ClosedSendChannelException)
        finish(22)
    }

    @Test
    fun testInitialValueAndReceiveClosed() = runTest {
        expect(1)
        val broadcast = ConflatedBroadcastChannel(1)
        assertEquals(1, broadcast.value)
        assertEquals(1, broadcast.valueOrNull)
        launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            val sub = broadcast.openSubscription()
            assertEquals(1, sub.receive())
            expect(3)
            assertTrue(exceptionFrom { sub.receive() } is ClosedReceiveChannelException) // suspends
            expect(6)
        }
        expect(4)
        broadcast.close()
        expect(5)
        yield() // to child
        finish(7)
    }

    private inline fun exceptionFrom(block: () -> Unit): Throwable? {
        return try {
            block()
            null
        } catch (e: Throwable) {
            e
        }
    }
}
