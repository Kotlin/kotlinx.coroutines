package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlinx.coroutines.experimental.io.internal.*
import kotlinx.coroutines.experimental.io.packet.*
import org.junit.*
import org.junit.rules.*
import java.nio.*
import java.util.*
import java.util.concurrent.*
import kotlin.test.*

class ByteBufferChannelTest {
    @get:Rule
    val timeout = Timeout(10, TimeUnit.SECONDS)

    @get:Rule
    val failures = ErrorCollector()

    private val Size = BufferSize - ByteBufferChannel.ReservedSize
    private val ch = ByteBufferChannel(autoFlush = false, pool = DirectBufferNoPool)

    @Test
    fun testBoolean() {
        runBlocking {
            ch.writeBoolean(true)
            ch.flush()
            assertEquals(true, ch.readBoolean())

            ch.writeBoolean(false)
            ch.flush()
            assertEquals(false, ch.readBoolean())
        }
    }

    @Test
    fun testByte() {
        runBlocking {
            assertEquals(0, ch.remaining)
            ch.writeByte(-1)
            ch.flush()
            assertEquals(1, ch.remaining)
            assertEquals(-1, ch.readByte())
            assertEquals(0, ch.remaining)
        }
    }

    @Test
    fun testUByte() {
        runBlocking {
            assertEquals(0, ch.remaining)
            ch.writeByte(255)
            ch.flush()
            assertEquals(1, ch.remaining)
            assertEquals(255, ch.readUByte())
            assertEquals(0, ch.remaining)
        }
    }

    @Test
    fun testShortB() {
        runBlocking {
            ch.readByteOrder = ByteOrder.BIG_ENDIAN
            ch.writeByteOrder = ByteOrder.BIG_ENDIAN

            assertEquals(0, ch.remaining)
            ch.writeShort(-1)
            assertEquals(0, ch.remaining)
            ch.flush()
            assertEquals(2, ch.remaining)
            assertEquals(-1, ch.readShort())
            assertEquals(0, ch.remaining)
        }
    }

    @Test
    fun testShortL() {
        runBlocking {
            ch.readByteOrder = ByteOrder.LITTLE_ENDIAN
            ch.writeByteOrder = ByteOrder.LITTLE_ENDIAN

            assertEquals(0, ch.remaining)
            ch.writeShort(-1)
            assertEquals(0, ch.remaining)
            ch.flush()
            assertEquals(2, ch.remaining)
            assertEquals(-1, ch.readShort())
            assertEquals(0, ch.remaining)
        }
    }

    @Test
    fun testUShortB() {
        runBlocking {
            ch.readByteOrder = ByteOrder.BIG_ENDIAN
            ch.writeByteOrder = ByteOrder.BIG_ENDIAN

            assertEquals(0, ch.remaining)
            ch.writeShort(0xffff)
            ch.flush()
            assertEquals(2, ch.remaining)
            assertEquals(0xffff, ch.readUShort())
            assertEquals(0, ch.remaining)
        }
    }

    @Test
    fun testUShortL() {
        runBlocking {
            ch.readByteOrder = ByteOrder.LITTLE_ENDIAN
            ch.writeByteOrder = ByteOrder.LITTLE_ENDIAN

            assertEquals(0, ch.remaining)
            ch.writeShort(0xffff)
            ch.flush()
            assertEquals(2, ch.remaining)
            assertEquals(0xffff, ch.readUShort())
            assertEquals(0, ch.remaining)
        }
    }

    @Test
    fun testShortEdge() {
        runBlocking {
            ch.writeByte(1)

            for (i in 2 until Size step 2) {
                ch.writeShort(0x00ee)
            }

            ch.flush()

            ch.readByte()
            ch.writeShort(0x1234)

            ch.flush()

            while (ch.remaining > 2) {
                ch.readShort()
            }

            assertEquals(0x1234, ch.readShort())
        }
    }

    @Test
    fun testIntB() {
        runBlocking {
            ch.readByteOrder = ByteOrder.BIG_ENDIAN
            ch.writeByteOrder = ByteOrder.BIG_ENDIAN

            assertEquals(0, ch.remaining)
            ch.writeInt(-1)
            ch.flush()
            assertEquals(4, ch.remaining)
            assertEquals(-1, ch.readInt())
            assertEquals(0, ch.remaining)
        }
    }

    @Test
    fun testIntL() {
        runBlocking {
            ch.readByteOrder = ByteOrder.LITTLE_ENDIAN
            ch.writeByteOrder = ByteOrder.LITTLE_ENDIAN

            assertEquals(0, ch.remaining)
            ch.writeInt(-1)
            ch.flush()
            assertEquals(4, ch.remaining)
            assertEquals(-1, ch.readInt())
            assertEquals(0, ch.remaining)
        }
    }

    @Test
    fun testUIntB() {
        runBlocking {
            ch.readByteOrder = ByteOrder.BIG_ENDIAN
            ch.writeByteOrder = ByteOrder.BIG_ENDIAN

            assertEquals(0, ch.remaining)
            ch.writeInt(0xffffffffL)
            ch.flush()
            assertEquals(4, ch.remaining)
            assertEquals(0xffffffffL, ch.readUInt())
            assertEquals(0, ch.remaining)
        }
    }

    @Test
    fun testUIntL() {
        runBlocking {
            ch.readByteOrder = ByteOrder.LITTLE_ENDIAN
            ch.writeByteOrder = ByteOrder.LITTLE_ENDIAN

            assertEquals(0, ch.remaining)
            ch.writeInt(0xffffffffL)
            ch.flush()
            assertEquals(4, ch.remaining)
            assertEquals(0xffffffffL, ch.readUInt())
            assertEquals(0, ch.remaining)
        }
    }

    @Test
    fun testIntEdge() {
        runBlocking {
            for (shift in 1..3) {
                for (i in 1..shift) {
                    ch.writeByte(1)
                }

                repeat(Size / 4 - 1) {
                    ch.writeInt(0xeeeeeeeeL)
                }

                ch.flush()

                for (i in 1..shift) {
                    ch.readByte()
                }

                ch.writeInt(0x12345678)

                ch.flush()

                while (ch.remaining > 4) {
                    ch.readInt()
                }

                assertEquals(0x12345678, ch.readInt())
            }
        }
    }

    @Test
    fun testLongB() {
        runBlocking {
            ch.readByteOrder = ByteOrder.BIG_ENDIAN
            ch.writeByteOrder = ByteOrder.BIG_ENDIAN

            assertEquals(0, ch.remaining)
            ch.writeLong(Long.MIN_VALUE)
            ch.flush()
            assertEquals(8, ch.remaining)
            assertEquals(Long.MIN_VALUE, ch.readLong())
            assertEquals(0, ch.remaining)
        }
    }

    @Test
    fun testLongL() {
        runBlocking {
            ch.readByteOrder = ByteOrder.LITTLE_ENDIAN
            ch.writeByteOrder = ByteOrder.LITTLE_ENDIAN

            assertEquals(0, ch.remaining)
            ch.writeLong(Long.MIN_VALUE)
            ch.flush()
            assertEquals(8, ch.remaining)
            assertEquals(Long.MIN_VALUE, ch.readLong())
            assertEquals(0, ch.remaining)
        }
    }

    @Test
    fun testLongEdge() {
        runBlocking {
            for (shift in 1..7) {
                for (i in 1..shift) {
                    ch.writeByte(1)
                }

                repeat(Size / 8 - 1) {
                    ch.writeLong(0x11112222eeeeeeeeL)
                }

                ch.flush()
                for (i in 1..shift) {
                    ch.readByte()
                }

                ch.writeLong(0x1234567812345678L)
                ch.flush()

                while (ch.remaining > 8) {
                    ch.readLong()
                }

                assertEquals(0x1234567812345678L, ch.readLong())
            }
        }
    }

    @Test
    fun testDoubleB() {
        runBlocking {
            ch.readByteOrder = ByteOrder.BIG_ENDIAN
            ch.writeByteOrder = ByteOrder.BIG_ENDIAN

            assertEquals(0, ch.remaining)
            ch.writeDouble(1.05)
            ch.flush()

            assertEquals(8, ch.remaining)
            assertEquals(1.05, ch.readDouble())
            assertEquals(0, ch.remaining)
        }
    }

    @Test
    fun testDoubleL() {
        runBlocking {
            ch.readByteOrder = ByteOrder.LITTLE_ENDIAN
            ch.writeByteOrder = ByteOrder.LITTLE_ENDIAN

            assertEquals(0, ch.remaining)
            ch.writeDouble(1.05)
            ch.flush()

            assertEquals(8, ch.remaining)
            assertEquals(1.05, ch.readDouble())
            assertEquals(0, ch.remaining)
        }
    }

    @Test
    fun testFloatB() {
        runBlocking {
            ch.readByteOrder = ByteOrder.BIG_ENDIAN
            ch.writeByteOrder = ByteOrder.BIG_ENDIAN

            assertEquals(0, ch.remaining)
            ch.writeFloat(1.05f)
            ch.flush()

            assertEquals(4, ch.remaining)
            assertEquals(1.05f, ch.readFloat())
            assertEquals(0, ch.remaining)
        }
    }

    @Test
    fun testFloatL() {
        runBlocking {
            ch.readByteOrder = ByteOrder.LITTLE_ENDIAN
            ch.writeByteOrder = ByteOrder.LITTLE_ENDIAN

            assertEquals(0, ch.remaining)
            ch.writeFloat(1.05f)
            ch.flush()

            assertEquals(4, ch.remaining)
            assertEquals(1.05f, ch.readFloat())
            assertEquals(0, ch.remaining)
        }
    }

    @Test
    fun testEndianMix() {
        runBlocking {
            for (writeOrder in ByteOrder.values()) {
                ch.writeByteOrder = writeOrder

                for (readOrder in ByteOrder.values()) {
                    ch.readByteOrder = readOrder

                    assertEquals(0, ch.remaining)
                    ch.writeShort(0x001f)
                    ch.flush()
                    if (writeOrder == readOrder)
                        assertEquals(0x001f, ch.readShort())
                    else
                        assertEquals(0x1f00, ch.readShort())

                    assertEquals(0, ch.remaining)
                    ch.writeShort(0x001f)
                    ch.flush()
                    if (writeOrder == readOrder)
                        assertEquals(0x001f, ch.readShort())
                    else
                        assertEquals(0x1f00, ch.readShort())

                    assertEquals(0, ch.remaining)
                    ch.writeInt(0x1f)
                    ch.flush()
                    if (writeOrder == readOrder)
                        assertEquals(0x0000001f, ch.readInt())
                    else
                        assertEquals(0x1f000000, ch.readInt())

                    assertEquals(0, ch.remaining)
                    ch.writeInt(0x1fL)
                    ch.flush()
                    if (writeOrder == readOrder)
                        assertEquals(0x0000001f, ch.readInt())
                    else
                        assertEquals(0x1f000000, ch.readInt())

                    assertEquals(0, ch.remaining)
                    ch.writeLong(0x1f)
                    ch.flush()
                    if (writeOrder == readOrder)
                        assertEquals(0x1f, ch.readLong())
                    else
                        assertEquals(0x1f00000000000000L, ch.readLong())
                }
            }
        }
    }

    @Test
    fun testClose() {
        runBlocking {
            ch.writeByte(1)
            ch.writeByte(2)
            ch.writeByte(3)

            ch.flush()
            assertEquals(1, ch.readByte())
            ch.close()

            assertEquals(2, ch.readByte())
            assertEquals(3, ch.readByte())

            try {
                ch.readByte()
                fail()
            } catch (expected: ClosedReceiveChannelException) {
            }
        }
    }

    @Test
    fun testReadAndWriteFully() {
        runBlocking {
            val bytes = byteArrayOf(1, 2, 3, 4, 5)
            val dst = ByteArray(5)

            ch.writeFully(bytes)
            ch.flush()
            assertEquals(5, ch.remaining)
            ch.readFully(dst)
            assertTrue { dst.contentEquals(bytes) }

            ch.writeFully(bytes)
            ch.flush()

            val dst2 = ByteArray(4)
            ch.readFully(dst2)

            assertEquals(1, ch.remaining)
            assertEquals(5, ch.readByte())

            ch.close()

            try {
                ch.readFully(dst)
                fail("")
            } catch (expected: ClosedReceiveChannelException) {
            }
        }
    }

    @Test
    fun testReadAndWriteFullyByteBuffer() {
        runBlocking {
            val bytes = byteArrayOf(1, 2, 3, 4, 5)
            val dst = ByteArray(5)

            ch.writeFully(ByteBuffer.wrap(bytes))
            ch.flush()
            assertEquals(5, ch.remaining)
            ch.readFully(ByteBuffer.wrap(dst))
            assertTrue { dst.contentEquals(bytes) }

            ch.writeFully(ByteBuffer.wrap(bytes))
            ch.flush()

            val dst2 = ByteArray(4)
            ch.readFully(ByteBuffer.wrap(dst2))

            assertEquals(1, ch.remaining)
            assertEquals(5, ch.readByte())

            ch.close()

            try {
                ch.readFully(ByteBuffer.wrap(dst))
                fail("")
            } catch (expected: ClosedReceiveChannelException) {
            }
        }
    }

    @Test
    fun testReadAndWritePartially() {
        runBlocking {
            val bytes = byteArrayOf(1, 2, 3, 4, 5)

            assertEquals(5, ch.writeLazy(bytes))
            ch.flush()
            assertEquals(5, ch.readLazy(ByteArray(100)))

            repeat(Size / bytes.size) {
                assertNotEquals(0, ch.writeLazy(bytes))
                ch.flush()
            }

            ch.readLazy(ByteArray(ch.remaining - 1))
            assertEquals(1, ch.readLazy(ByteArray(100)))

            ch.close()
        }
    }

    @Test
    fun testReadAndWritePartiallyByteBuffer() {
        runBlocking {
            val bytes = byteArrayOf(1, 2, 3, 4, 5)

            assertEquals(5, ch.writeLazy(ByteBuffer.wrap(bytes)))
            ch.flush()
            assertEquals(5, ch.readLazy(ByteBuffer.allocate(100)))

            repeat(Size / bytes.size) {
                assertNotEquals(0, ch.writeLazy(ByteBuffer.wrap(bytes)))
                ch.flush()
            }

            ch.readLazy(ByteArray(ch.remaining - 1))
            assertEquals(1, ch.readLazy(ByteBuffer.allocate(100)))

            ch.close()
        }
    }


    @Test
    fun testReadAndWriteBig() {
        val count = 200
        val bytes = ByteArray(65536)
        Random().nextBytes(bytes)

        launch(CommonPool + CoroutineName("writer")) {
            for (i in 1..count) {
                ch.writeFully(bytes)
                ch.flush()
            }
        }.invokeOnCompletion { t ->
            if (t != null) {
                failures.addError(t)
            }
        }

        runBlocking(CoroutineName("reader")) {
            val dst = ByteArray(bytes.size)
            for (i in 1..count) {
                ch.readFully(dst)
                assertTrue { dst.contentEquals(bytes) }
                dst.fill(0)
            }
        }
    }

    @Test
    fun testReadAndWriteBigByteBuffer() {
        val count = 200
        val bytes = ByteArray(65536)
        Random().nextBytes(bytes)

        launch(CommonPool + CoroutineName("writer")) {
            for (i in 1..count) {
                ch.writeFully(ByteBuffer.wrap(bytes))
                ch.flush()
            }
        }.invokeOnCompletion { t ->
            if (t != null) {
                failures.addError(t)
            }
        }

        runBlocking(CoroutineName("reader")) {
            val dst = ByteArray(bytes.size)
            for (i in 1..count) {
                ch.readFully(ByteBuffer.wrap(dst))
                assertTrue { dst.contentEquals(bytes) }
                dst.fill(0)
            }
        }
    }

    @Test
    fun testPacket() = runBlocking {
        val packet = buildPacket {
            writeInt(0xffee)
            writeUtf8String("Hello")
        }

        ch.writeInt(packet.remaining)
        ch.writePacket(packet)

        ch.flush()

        val size = ch.readInt()
        val readed = ch.readPacket(size)

        assertEquals(0xffee, readed.readInt())
        assertEquals("Hello", readed.readUTF8Line())
    }

    @Test
    fun testBigPacket() = runBlocking {
        launch(CommonPool + CoroutineName("writer")) {
            val packet = buildPacket {
                writeInt(0xffee)
                writeUtf8String(".".repeat(8192))
            }

            ch.writeInt(packet.remaining)
            ch.writePacket(packet)

            ch.flush()
        }

        val size = ch.readInt()
        val readed = ch.readPacket(size)

        assertEquals(0xffee, readed.readInt())
        assertEquals(".".repeat(8192), readed.readUTF8Line())
    }
}