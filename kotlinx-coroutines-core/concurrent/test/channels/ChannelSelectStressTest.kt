//package kotlinx.coroutines.channels
//
//import kotlinx.atomicfu.*
//import kotlinx.coroutines.*
//import kotlinx.coroutines.selects.*
//import kotlinx.coroutines.testing.*
//import kotlin.coroutines.cancellation.CancellationException
//import kotlin.test.*
//
//class ChannelSelectStressTest : TestBase() {
//    private val pairedCoroutines = 3
//    private val dispatcher = newFixedThreadPoolContext(pairedCoroutines * 2, "ChannelSelectStressTest")
//    private val elementsToSend = 20_000 * Long.SIZE_BITS * stressTestMultiplier
//    private val sent = atomic(0)
//    private val received = atomic(0)
//    private val receivedArray = AtomicLongArray(elementsToSend / Long.SIZE_BITS)
//    private val channel = Channel<Int>()
//
//    @AfterTest
//    fun tearDown() {
//        dispatcher.close()
//    }
//
//    @Test
//    fun testAtomicCancelStress() = runTest {
//        withContext(dispatcher) {
//            repeat(pairedCoroutines) { launchSender() }
//            repeat(pairedCoroutines) { launchReceiver() }
//        }
//        val missing = ArrayList<Int>()
//        for (i in 0 until receivedArray.size) {
//            val bits = receivedArray[i].value
//            if (bits != 0L.inv()) {
//                for (j in 0 until Long.SIZE_BITS) {
//                    val mask = 1L shl j
//                    if (bits and mask == 0L) missing += i * Long.SIZE_BITS + j
//                }
//            }
//        }
//        if (missing.isNotEmpty()) {
//            fail("Missed ${missing.size} out of $elementsToSend: $missing")
//        }
//    }
//
//    private fun CoroutineScope.launchSender() {
//        launch {
//            while (sent.value < elementsToSend) {
//                val element = sent.getAndIncrement()
//                if (element >= elementsToSend) break
//                select { channel.onSend(element) {} }
//            }
//            channel.close(CancellationException())
//        }
//    }
//
//    private fun CoroutineScope.launchReceiver() {
//        launch {
//            while (received.value != elementsToSend) {
//                val element = select<Int> { channel.onReceive { it } }
//                received.incrementAndGet()
//                val index = (element / Long.SIZE_BITS)
//                val mask = 1L shl (element % Long.SIZE_BITS.toLong()).toInt()
//                while (true) {
//                    val bits = receivedArray[index].value
//                    if (bits and mask != 0L) {
//                        error("Detected duplicate")
//                    }
//                    val newBits = bits or mask
//                    if (receivedArray[index].compareAndSet(bits, newBits)) break
//                }
//            }
//        }
//    }
//}
