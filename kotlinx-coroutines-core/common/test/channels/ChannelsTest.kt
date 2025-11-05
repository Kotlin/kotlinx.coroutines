@file:Suppress("DEPRECATION")

package kotlinx.coroutines.channels

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.math.*
import kotlin.test.*

class ChannelsTest: TestBase() {
    private val testList = listOf(1, 2, 3)

    @Test
    fun testIterableAsReceiveChannel() = runTest {
        assertEquals(testList, testList.asReceiveChannel().toList())
    }

    @Test
    fun testCloseWithMultipleSuspendedReceivers() = runTest {
        // Once the channel is closed, the waiting
        // requests should be cancelled in the order
        // they were suspended in the channel.
        val channel = Channel<Int>()
        launch {
            try {
                expect(2)
                channel.receive()
                expectUnreached()
            } catch (e: ClosedReceiveChannelException) {
                expect(5)
            }
        }

        launch {
            try {
                expect(3)
                channel.receive()
                expectUnreached()
            } catch (e: ClosedReceiveChannelException) {
                expect(6)
            }
        }

        expect(1)
        yield()
        expect(4)
        channel.close()
        yield()
        finish(7)
    }

    @Test
    fun testCloseWithMultipleSuspendedSenders() = runTest {
        // Once the channel is closed, the waiting
        // requests should be cancelled in the order
        // they were suspended in the channel.
        val channel = Channel<Int>()
        launch {
            try {
                expect(2)
                channel.send(42)
                expectUnreached()
            } catch (e: CancellationException) {
                expect(5)
            }
        }

        launch {
            try {
                expect(3)
                channel.send(42)
                expectUnreached()
            } catch (e: CancellationException) {
                expect(6)
            }
        }

        expect(1)
        yield()
        expect(4)
        channel.cancel()
        yield()
        finish(7)
    }

    @Test
    fun testEmptyToList() = runTest {
        assertTrue(emptyList<Nothing>().asReceiveChannel().toList().isEmpty())
    }

    @Test
    fun testToList() = runTest {
        assertEquals(testList, testList.asReceiveChannel().toList())
    }

    @Test
    fun testToListOnFailedChannel() = runTest {
        val channel = Channel<Int>()
        channel.close(TestException())
        assertFailsWith<TestException> {
            channel.toList()
        }
    }

    @Test
    fun testEmptyConsumeToWithDestination() = runTest {
        val initialList = listOf(-1, -2, -3)
        val destination = initialList.toMutableList()
        emptyList<Nothing>().asReceiveChannel().consumeTo(destination)
        assertEquals(initialList, destination)
    }

    @Test
    fun testConsumeToWithDestination() = runTest {
        val initialList = listOf(-1, -2, -3)
        val destination = initialList.toMutableList()
        testList.asReceiveChannel().consumeTo(destination)
        assertEquals(initialList + testList, destination)
    }

    @Test
    fun testConsumeToWithDestinationOnFailedChannel() = runTest {
        val initialList = listOf(-1, -2, -3)
        val destination = initialList.toMutableList()
        val channel = Channel<Int>(10)
        val elementsToSend = (1..5)
        elementsToSend.forEach {
            val result = channel.trySend(it)
            assertTrue(result.isSuccess)
        }
        channel.close(TestException())
        assertFailsWith<TestException> {
            channel.consumeTo(destination)
        }
        assertEquals(initialList + elementsToSend, destination)
    }

    private fun <E> Iterable<E>.asReceiveChannel(context: CoroutineContext = Dispatchers.Unconfined): ReceiveChannel<E> =
        GlobalScope.produce(context) {
            for (element in this@asReceiveChannel)
                send(element)
        }
}
