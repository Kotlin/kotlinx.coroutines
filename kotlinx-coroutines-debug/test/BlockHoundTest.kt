package kotlinx.coroutines.debug
import kotlinx.coroutines.*
import kotlinx.coroutines.debug.internal.BlockHoundIntegration
import org.junit.*
import reactor.blockhound.BlockingOperationError

class BlockHoundTest : TestBase() {

    @Before
    fun init() {
        BlockHoundIntegration.install()
    }

    @After
    fun deinit() {
        BlockHoundIntegration.uninstall()
    }

    @Test(expected = BlockingOperationError::class)
    fun shouldDetectBlockingInDefault() = runTest {
        withContext(Dispatchers.Default) {
            Thread.sleep(1)
        }
    }

    @Test
    fun shouldNotDetectBlockingInIO() = runTest {
        withContext(Dispatchers.IO) {
            Thread.sleep(1)
        }
    }

    @Test
    fun shouldNotDetectNonblocking() = runTest {
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
