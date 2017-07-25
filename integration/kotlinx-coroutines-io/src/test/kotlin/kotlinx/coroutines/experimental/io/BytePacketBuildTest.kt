package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.io.packet.*
import org.junit.*
import kotlin.test.*

class BytePacketBuildTest {
    @Test
    fun name() {
        val p = buildPacket {
            writeInt(0x12345678)
            writeUtf8String("OK\n")
            listOf(1, 2, 3).joinTo(this, separator = "|")
        }

        assertEquals(12, p.remaining)

        assertEquals(0x12345678, p.readInt())
        assertEquals("OK", p.readUTF8Line())
        assertEquals("1,2,3", p.readUTF8Line())
    }
}