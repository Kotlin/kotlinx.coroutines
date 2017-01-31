package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import org.junit.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class RendezvousChannelTest : TestBase() {
    @Test
    fun testSimple() = runBlocking {
        val q = RendezvousChannel<Int>()
        check(q.isEmpty && q.isFull)
        expect(1)
        val sender = launch(context) {
            expect(4)
            q.send(1) // suspend -- the first to come to rendezvous
            expect(7)
            q.send(2) // does not suspend -- receiver is there
            expect(8)
        }
        expect(2)
        val receiver = launch(context) {
            expect(5)
            check(q.receive() == 1) // does not suspend -- sender was there
            expect(6)
            check(q.receive() == 2) // suspends
            expect(9)
        }
        expect(3)
        sender.join()
        receiver.join()
        check(q.isEmpty && q.isFull)
        finish(10)
    }

    @Test
    fun testStress() = runBlocking {
        val n = 100_000
        val q = RendezvousChannel<Int>()
        val sender = launch(context) {
            for (i in 1..n) q.send(i)
            expect(2)
        }
        val receiver = launch(context) {
            for (i in 1..n) check(q.receive() == i)
            expect(3)
        }
        expect(1)
        sender.join()
        receiver.join()
        finish(4)
    }

    @Test
    fun testClosedReceiveOrNull() = runBlocking {
        val q = RendezvousChannel<Int>()
        check(q.isEmpty && q.isFull && !q.isClosedForSend && !q.isClosedForReceive)
        expect(1)
        launch(context) {
            expect(3)
            assertEquals(42, q.receiveOrNull())
            expect(4)
            assertEquals(null, q.receiveOrNull())
            expect(6)
        }
        expect(2)
        q.send(42)
        expect(5)
        q.close()
        check(!q.isEmpty && !q.isFull && q.isClosedForSend && q.isClosedForReceive)
        yield()
        check(!q.isEmpty && !q.isFull && q.isClosedForSend && q.isClosedForReceive)
        finish(7)
    }

    @Test
    fun testClosedExceptions() = runBlocking {
        val q = RendezvousChannel<Int>()
        expect(1)
        launch(context) {
            expect(4)
            try { q.receive() }
            catch (e: ClosedReceiveChannelException) {
                expect(5)
            }
        }
        expect(2)
        q.close()
        expect(3)
        yield()
        expect(6)
        try { q.send(42) }
        catch (e: ClosedSendChannelException) {
            finish(7)
        }
    }

    @Test
    fun testOfferAndPool() = runBlocking {
        val q = RendezvousChannel<Int>()
        assertFalse(q.offer(1))
        expect(1)
        launch(context) {
            expect(3)
            assertEquals(null, q.pool())
            expect(4)
            assertEquals(2, q.receive())
            expect(7)
            assertEquals(null, q.pool())
            yield()
            expect(9)
            assertEquals(3, q.pool())
            expect(10)
        }
        expect(2)
        yield()
        expect(5)
        assertTrue(q.offer(2))
        expect(6)
        yield()
        expect(8)
        q.send(3)
        finish(11)
    }
}