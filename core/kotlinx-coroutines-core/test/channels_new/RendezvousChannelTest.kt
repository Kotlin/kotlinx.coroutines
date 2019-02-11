package channels_new

import kotlinx.coroutines.*
import kotlin.test.*
import java.util.concurrent.Phaser

abstract class AbstractRendezvousChannelTest : TestBase() {
    abstract fun newChannel(): Channel<Int>

    @Test
    fun `simple test`() = runTest {
        val q = newChannel()
        expect(1)
        val sender = launch {
            expect(4)
            println("SENDING 1...")
            q.send(1) // suspend -- the first to come to rendezvous
            println("SENT 1")
            expect(7)
            println("SENDING 2...")
            q.send(2) // does not suspend -- receiver is there
            println("SENT 2")
            println("SENT 2")
            expect(8)
        }
        expect(2)
        val receiver = launch {
            expect(5)
            println("RECEIVING...")
            check(q.receive() == 1) // does not suspend -- sender was there
            println("RECEIVED 1")
            expect(6)
            println("RECEIVING...")
            check(q.receive() == 2) // suspends
            println("RECEIVED 2")
            expect(9)
        }
        expect(3)
        sender.join()
        receiver.join()
        finish(10)
    }

//    @Ignore
    @Test
    fun `test offer() and poll()`() = runTest {
        val q = newChannel()
        assertFalse(q.offer(1))
        expect(1)
        launch {
            expect(3)
            assertEquals(null, q.poll())
            expect(4)
            assertEquals(2, q.receive())
            expect(7)
            assertEquals(null, q.poll())
            yield()
            expect(9)
            assertEquals(3, q.poll())
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

    @Test
    fun `SPSC stress test`() = runTest {
        val n = 100_000
        val q = newChannel()
        val sender = launch {
            for (i in 1..n) q.send(i)
            expect(2)
        }
        val receiver = launch {
            for (i in 1..n) check(q.receive() == i)
            expect(3)
        }
        expect(1)
        sender.join()
        receiver.join()
        finish(4)
    }

    @Test
    fun `MPMC stress test`() {
        val n = 100_000
        val k = 10
        val q = newChannel()
        val done = Phaser(2 * k + 1)
        repeat(k) {
            GlobalScope.launch {
                for (i in 1..n) q.send(i)
                done.arrive()
            }
        }
        repeat(k) {
            GlobalScope.launch {
                for (i in 1..n) q.receive()
                done.arrive()
            }
        }
        done.arriveAndAwaitAdvance()
    }
}

class RendezvousChannelTest  : AbstractRendezvousChannelTest() {
    override fun newChannel() = RendezvousChannel<Int>()
}

class RendezvousChannelMSQueueTest  : AbstractRendezvousChannelTest() {
    override fun newChannel() = RendezvousChannelMSQueue<Int>()
}

class RendezvousChannelStackTest  : AbstractRendezvousChannelTest() {
    override fun newChannel() = RendezvousChannelStack<Int>()
}