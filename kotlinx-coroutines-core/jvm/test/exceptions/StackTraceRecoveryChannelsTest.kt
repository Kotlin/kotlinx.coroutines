package kotlinx.coroutines.exceptions

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*
import org.junit.Rule
import org.junit.rules.*
import kotlin.coroutines.*

class StackTraceRecoveryChannelsTest : TestBase() {

    @get:Rule
    val name = TestName()

    @Test
    fun testReceiveFromChannel() = runTest {
        val channel = Channel<Int>()
        val job = launch {
            expect(2)
            channel.close(RecoverableTestException())
        }

        expect(1)
        channelReceive(channel)
        expect(3)
        job.join()
        finish(4)
    }

    @Test
    fun testReceiveFromClosedChannel() = runTest {
        val channel = Channel<Int>()
        channel.close(RecoverableTestException())
        channelReceive(channel)
    }

    @Test
    fun testSendToClosedChannel() = runTest {
        val channel = Channel<Int>()
        channel.close(RecoverableTestException())
        channelSend(channel)
    }

    @Test
    fun testSendToChannel() = runTest {
        val channel = Channel<Int>()
        val job = launch {
            expect(2)
            channel.cancel()
        }

        expect(1)
        channelSend(channel)
        expect(3)
        job.join()
        finish(4)
    }

    private suspend fun channelReceive(channel: Channel<Int>) = channelOp { channel.receive() }

    private suspend inline fun channelOp(block: () -> Any?) {
        yield()
        val e = assertFailsWith<RecoverableTestException> {
            block()
        }
        verifyStackTrace("channels/${name.methodName}", e)
    }

    private suspend fun channelSend(channel: Channel<Int>) {
        yield()
        val e = assertFailsWith<Exception> {
            channel.send(1)
        }
        verifyStackTrace("channels/${name.methodName}", e)
    }

    @Test
    fun testOfferWithCurrentContext() = runTest {
        val channel = Channel<Int>()
        channel.close(RecoverableTestException())

        val e = assertFailsWith<RecoverableTestException> {
            channel.sendWithContext(coroutineContext)
        }
        verifyStackTrace("channels/${name.methodName}", e)
    }

    @Test
    fun testOfferWithContextWrapped() = runTest {
        val channel = Channel<Int>()
        channel.close(RecoverableTestException())
        val e = assertFailsWith<RecoverableTestException> {
            channel.sendWithContext(wrapperDispatcher(coroutineContext))
        }
        verifyStackTrace("channels/${name.methodName}", e)
    }

    @Test
    fun testOfferFromScope() = runTest {
        val channel = Channel<Int>()
        channel.close(RecoverableTestException())
        val e = assertFailsWith<RecoverableTestException> {
            channel.sendFromScope()
        }
        verifyStackTrace("channels/${name.methodName}", e)
    }

    // Slow path via suspending send
    @Test
    fun testSendFromScope() = runTest {
        val channel = Channel<Int>()
        val deferred = async {
            expect(1)
            val e = assertFailsWith<Exception> {
                channel.sendFromScope()
            }
            verifyStackTrace("channels/${name.methodName}", e)
        }
        yield()
        expect(2)
        // Cancel is an analogue of `produce` failure, just a shorthand
        channel.cancel(RecoverableTestCancellationException())
        finish(3)
        deferred.await()
    }

    private suspend fun Channel<Int>.sendWithContext(ctx: CoroutineContext) = withContext(ctx) {
        sendInChannel()
        yield() // TCE
    }

    private suspend fun Channel<Int>.sendInChannel() {
        send(42)
        yield() // TCE
    }

    private suspend fun Channel<Int>.sendFromScope() = coroutineScope {
        sendWithContext(wrapperDispatcher(coroutineContext))
    }
}
