package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

class BasicOperationsTest : TestBase() {

    @Test
    fun testSimpleSendReceive() = testChannel {
        // Parametrized common test :(
        val channel = it.create()
        launch(coroutineContext) {
            repeat(100) { channel.send(it) }
            channel.close()
        }
        var expected = 0
        for (x in channel) {
            if (!it.isConflated) {
                assertEquals(expected++, x, "Type: $it")
            } else {
                assertTrue(x >= expected, "Type: $it")
                expected = x + 1
            }
        }
        if (!it.isConflated) {
            assertEquals(100, expected, "Type: $it")
        }
    }

    @Test
    fun testOfferAfterClose() = testChannel {
        val channel = it.create()
        val d = async(coroutineContext) { channel.send(42) }
        yield()
        channel.close()
        assertTrue(channel.isClosedForSend)
        try {
            channel.offer(2)
            fail()
        } catch (e: ClosedSendChannelException) {
            if (!it.isConflated) {
                assertEquals(42, channel.receive())
            }
        }
        d.await()
    }

    @Test
    fun testReceiveOrNullAfterClose() = testChannel {
        val channel = it.create()
        val d = async(coroutineContext) {
            channel.receive()
        }
        yield()
        channel.close()
        assertTrue(channel.isClosedForReceive)
        assertNull(channel.receiveOrNull())
        assertNull(channel.poll())
        assertFailsWith<ClosedReceiveChannelException>(d)
    }

    @Test
    fun testReceiveOrNullAfterCloseWithException() = testChannel {
        testReceiveOrNullException(it)
    }

    @Test
    fun testJobCompletion() = testChannel() {
        var channel: Channel<Int>? = null
        val producer = async(coroutineContext) {
            channel = it.create(coroutineContext[Job]!!)
            channel!!.send(1)
        }
        val consumer = async(coroutineContext) {
            for (element in channel!!) {
                assertEquals(1, element)
            }
        }
        producer.await()
        consumer.await()
    }

    @Test
    fun testJobCancellationWithoutCause() = testChannel {
        testJobCancellation<JobCancellationException>(it)
    }

    @Test
    fun testJobCancellationWithCause() = testChannel {
        testJobCancellation(it, IllegalStateException())
    }

    private suspend inline fun <reified T : Exception> testJobCancellation(kind: TestChannelKind, exception: T? = null) {
        var channel: Channel<Int>? = null
        val producer = async(coroutineContext) {
            channel = kind.create(coroutineContext[Job]!!)

            while (true) {
                channel!!.send(1)
                yield()
            }
        }

        val consumer = async(coroutineContext) {
            for (element in channel!!) {
                val value = channel!!.receive()
                assertEquals(1, value)
            }
        }

        yield()
        producer.cancel(exception)
        assertFailsWith<T>(producer)
        assertFailsWith<T>(consumer)
    }

    private suspend fun testReceiveOrNullException(kind: TestChannelKind) {
        val channel = kind.create()
        val d = async(coroutineContext) {
            channel.receive()
        }

        yield()
        channel.close(IndexOutOfBoundsException())
        assertTrue(channel.isClosedForReceive)

        assertFails<IndexOutOfBoundsException> { channel.poll() }
        assertFails<IndexOutOfBoundsException> { channel.receiveOrNull() }
        assertFailsWith<IndexOutOfBoundsException>(d)
    }

    // Parametrized common test :(
    private fun testChannel(block: suspend CoroutineScope.(TestChannelKind) -> Unit) {
        TestChannelKind.values().forEach { kind -> runTest { block(kind) } }
    }
}
