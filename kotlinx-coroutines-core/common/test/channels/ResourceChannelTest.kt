package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.test.*

class ResourceChannelTest : TestBase() {
    @Test
    fun testSendSuccessfully() = runAllKindsTest { kind ->
        val channel = kind.create<Resource<String>>()
        val res = Resource("OK") {}
        launch {
            channel.send(res)
        }
        val ok = channel.receive()
        assertEquals("OK", ok.value)
        assertFalse(res.isCancelled) // was not cancelled
        channel.close()
        assertFalse(res.isCancelled) // still was not cancelled
    }

    @Test
    fun testRendezvousSendCancelled() = runTest {
        val channel = Channel<Resource<String>>()
        val res = Resource("OK") {}
        val sender = launch(start = CoroutineStart.UNDISPATCHED) {
            assertFailsWith<CancellationException> {
                channel.send(res) // suspends & get cancelled
            }
        }
        sender.cancelAndJoin()
        assertTrue(res.isCancelled)
    }

    @Test
    fun testBufferedSendCancelled() = runTest {
        val channel = Channel<Resource<String>>(1)
        val resA = Resource("A") {}
        val resB = Resource("B") {}
        val sender = launch(start = CoroutineStart.UNDISPATCHED) {
            channel.send(resA) // goes to buffer
            assertFailsWith<CancellationException> {
                channel.send(resB) // suspends & get cancelled
            }
        }
        sender.cancelAndJoin()
        assertFalse(resA.isCancelled) // it is in buffer, not cancelled
        assertTrue(resB.isCancelled) // send was cancelled
        channel.cancel() // now cancel the channel
        assertTrue(resA.isCancelled) // now cancelled in buffer
    }

    @Test
    fun testConflatedResourceCancelled() = runTest {
        val channel = Channel<Resource<String>>(Channel.CONFLATED)
        val resA = Resource("A") {}
        val resB = Resource("B") {}
        channel.send(resA)
        assertFalse(resA.isCancelled)
        assertFalse(resB.isCancelled)
        channel.send(resB)
        assertTrue(resA.isCancelled) // it was conflated (lost) and thus cancelled
        assertFalse(resB.isCancelled)
        channel.close()
        assertFalse(resB.isCancelled) // not cancelled yet, can be still read by receiver
        channel.cancel()
        assertTrue(resB.isCancelled) // now it is cancelled
    }

    @Test
    fun testSendToClosedChannel() = runAllKindsTest { kind ->
        val channel = kind.create<Resource<String>>()
        channel.close() // immediately close channel
        val res = Resource("OK") {}
        assertFailsWith<ClosedSendChannelException> {
            channel.send(res) // send fails to closed channel
        }
        assertFalse(res.isCancelled) // that's not a cancellation! Resource is not cancelled
    }

    private fun runAllKindsTest(test: suspend CoroutineScope.(TestChannelKind) -> Unit) {
        for (kind in TestChannelKind.values()) {
            try {
                runTest {
                    test(kind)
                }
            } catch(e: Throwable) {
                error("$kind: $e", e)
            }
        }
    }
}