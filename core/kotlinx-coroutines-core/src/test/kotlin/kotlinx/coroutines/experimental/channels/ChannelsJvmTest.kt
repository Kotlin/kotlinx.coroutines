package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import org.junit.Test
import kotlin.test.*

class ChannelsJvmTest : TestBase() {

    @Test
    fun testBlocking() {
        val ch = Channel<Int>()
        val sum = async {
            ch.sumBy { it }
        }
        repeat(10) {
            ch.sendBlocking(it)
        }
        ch.close()
        assertEquals(45, runBlocking { sum.await() })
    }
}
