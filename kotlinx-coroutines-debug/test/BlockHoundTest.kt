package kotlinx.coroutines.debug
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.junit.*
import reactor.blockhound.*

@Suppress("UnusedEquals", "DeferredResultUnused", "BlockingMethodInNonBlockingContext")
class BlockHoundTest : TestBase() {

    @Before
    fun init() {
        BlockHound.install()
    }

    @Test(expected = BlockingOperationError::class)
    fun testShouldDetectBlockingInDefault() = runTest {
        withContext(Dispatchers.Default) {
            Thread.sleep(1)
        }
    }

    @Test
    fun testShouldNotDetectBlockingInIO() = runTest {
        withContext(Dispatchers.IO) {
            Thread.sleep(1)
        }
    }

    @Test
    fun testShouldNotDetectNonblocking() = runTest {
        withContext(Dispatchers.Default) {
            val a = 1
            val b = 2
            assert(a + b == 3)
        }
    }

    @Test
    fun testReusingThreads() = runTest {
        val n = 100
        repeat(n) {
            async(Dispatchers.IO) {
                Thread.sleep(1)
            }
        }
        repeat(n) {
            async(Dispatchers.Default) {
            }
        }
        repeat(n) {
            async(Dispatchers.IO) {
                Thread.sleep(1)
            }
        }
    }

    @Test
    fun testChannelNotBeingConsideredBlocking() = runTest {
        withContext(Dispatchers.Default) {
            // Copy of kotlinx.coroutines.channels.ArrayChannelTest.testSimple
            val q = Channel<Int>(1)
            check(q.isEmpty)
            check(!q.isClosedForReceive)
            check(!q.isClosedForSend)
            val sender = launch {
                q.send(1)
                q.send(2)
            }
            val receiver = launch {
                q.receive() == 1
                q.receive() == 2
            }
            sender.join()
            receiver.join()
        }
    }

    @Test
    fun testConflatedChannelsNotBeingConsideredBlocking() = runTest {
        withContext(Dispatchers.Default) {
            val q = Channel<Int>(Channel.CONFLATED)
            check(q.isEmpty)
            check(!q.isClosedForReceive)
            check(!q.isClosedForSend)
            val sender = launch {
                q.send(1)
            }
            val receiver = launch {
                q.receive() == 1
            }
            sender.join()
            receiver.join()
        }
    }

    @Test(expected = BlockingOperationError::class)
    fun testReusingThreadsFailure() = runTest {
        val n = 100
        repeat(n) {
            async(Dispatchers.IO) {
                Thread.sleep(1)
            }
        }
        async(Dispatchers.Default) {
            Thread.sleep(1)
        }
        repeat(n) {
            async(Dispatchers.IO) {
                Thread.sleep(1)
            }
        }
    }

}
