package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.CommonPool
import kotlinx.coroutines.experimental.CoroutineName
import kotlinx.coroutines.experimental.channels.ClosedReceiveChannelException
import kotlinx.coroutines.experimental.io.buffers.*
import kotlinx.coroutines.experimental.io.internal.BUFFER_SIZE
import kotlinx.coroutines.experimental.io.internal.BufferObjectNoPool
import kotlinx.coroutines.experimental.io.internal.RESERVED_SIZE
import kotlinx.coroutines.experimental.io.packet.*
import kotlinx.coroutines.experimental.launch
import kotlinx.coroutines.experimental.runBlocking
import org.junit.Rule
import org.junit.Test
import org.junit.rules.ErrorCollector
import org.junit.rules.Timeout
import java.nio.ByteBuffer
import java.nio.CharBuffer
import java.util.*
import java.util.concurrent.TimeUnit
import kotlin.test.assertEquals
import kotlin.test.assertNotEquals
import kotlin.test.assertTrue
import kotlin.test.fail

class ByteBufferChannelTest {
    @get:Rule
    val timeout = Timeout(10, TimeUnit.SECONDS)

    @get:Rule
    private val failures = ErrorCollector()

    @get:Rule
    private val pool = VerifyingObjectPool(BufferObjectNoPool)

    @get:Rule
    private val pktPool = VerifyingObjectPool(BufferView.Pool)

    private val Size = BUFFER_SIZE - RESERVED_SIZE
    private val ch = ByteBufferChannel(autoFlush = false, pool = pool)

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
            assertEquals(0, ch.availableForRead)
            ch.writeByte(-1)
            ch.flush()
            assertEquals(1, ch.availableForRead)
            assertEquals(-1, ch.readByte())
            assertEquals(0, ch.availableForRead)
        }
    }

    @Test
    fun testShortB() {
        runBlocking {
            ch.readByteOrder = ByteOrder.BIG_ENDIAN
            ch.writeByteOrder = ByteOrder.BIG_ENDIAN

            assertEquals(0, ch.availableForRead)
            ch.writeShort(-1)
            assertEquals(0, ch.availableForRead)
            ch.flush()
            assertEquals(2, ch.availableForRead)
            assertEquals(-1, ch.readShort())
            assertEquals(0, ch.availableForRead)
        }
    }

    @Test
    fun testShortL() {
        runBlocking {
            ch.readByteOrder = ByteOrder.LITTLE_ENDIAN
            ch.writeByteOrder = ByteOrder.LITTLE_ENDIAN

            assertEquals(0, ch.availableForRead)
            ch.writeShort(-1)
            assertEquals(0, ch.availableForRead)
            ch.flush()
            assertEquals(2, ch.availableForRead)
            assertEquals(-1, ch.readShort())
            assertEquals(0, ch.availableForRead)
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

            while (ch.availableForRead > 2) {
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

            assertEquals(0, ch.availableForRead)
            ch.writeInt(-1)
            ch.flush()
            assertEquals(4, ch.availableForRead)
            assertEquals(-1, ch.readInt())
            assertEquals(0, ch.availableForRead)
        }
    }

    @Test
    fun testIntL() {
        runBlocking {
            ch.readByteOrder = ByteOrder.LITTLE_ENDIAN
            ch.writeByteOrder = ByteOrder.LITTLE_ENDIAN

            assertEquals(0, ch.availableForRead)
            ch.writeInt(-1)
            ch.flush()
            assertEquals(4, ch.availableForRead)
            assertEquals(-1, ch.readInt())
            assertEquals(0, ch.availableForRead)
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

                while (ch.availableForRead > 4) {
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

            assertEquals(0, ch.availableForRead)
            ch.writeLong(Long.MIN_VALUE)
            ch.flush()
            assertEquals(8, ch.availableForRead)
            assertEquals(Long.MIN_VALUE, ch.readLong())
            assertEquals(0, ch.availableForRead)
        }
    }

    @Test
    fun testLongL() {
        runBlocking {
            ch.readByteOrder = ByteOrder.LITTLE_ENDIAN
            ch.writeByteOrder = ByteOrder.LITTLE_ENDIAN

            assertEquals(0, ch.availableForRead)
            ch.writeLong(Long.MIN_VALUE)
            ch.flush()
            assertEquals(8, ch.availableForRead)
            assertEquals(Long.MIN_VALUE, ch.readLong())
            assertEquals(0, ch.availableForRead)
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

                while (ch.availableForRead > 8) {
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

            assertEquals(0, ch.availableForRead)
            ch.writeDouble(1.05)
            ch.flush()

            assertEquals(8, ch.availableForRead)
            assertEquals(1.05, ch.readDouble())
            assertEquals(0, ch.availableForRead)
        }
    }

    @Test
    fun testDoubleL() {
        runBlocking {
            ch.readByteOrder = ByteOrder.LITTLE_ENDIAN
            ch.writeByteOrder = ByteOrder.LITTLE_ENDIAN

            assertEquals(0, ch.availableForRead)
            ch.writeDouble(1.05)
            ch.flush()

            assertEquals(8, ch.availableForRead)
            assertEquals(1.05, ch.readDouble())
            assertEquals(0, ch.availableForRead)
        }
    }

    @Test
    fun testFloatB() {
        runBlocking {
            ch.readByteOrder = ByteOrder.BIG_ENDIAN
            ch.writeByteOrder = ByteOrder.BIG_ENDIAN

            assertEquals(0, ch.availableForRead)
            ch.writeFloat(1.05f)
            ch.flush()

            assertEquals(4, ch.availableForRead)
            assertEquals(1.05f, ch.readFloat())
            assertEquals(0, ch.availableForRead)
        }
    }

    @Test
    fun testFloatL() {
        runBlocking {
            ch.readByteOrder = ByteOrder.LITTLE_ENDIAN
            ch.writeByteOrder = ByteOrder.LITTLE_ENDIAN

            assertEquals(0, ch.availableForRead)
            ch.writeFloat(1.05f)
            ch.flush()

            assertEquals(4, ch.availableForRead)
            assertEquals(1.05f, ch.readFloat())
            assertEquals(0, ch.availableForRead)
        }
    }



    @Test
    fun testEndianMix() {
        val byteOrders = listOf(ByteOrder.BIG_ENDIAN, ByteOrder.LITTLE_ENDIAN)
        runBlocking {
            for (writeOrder in byteOrders) {
                ch.writeByteOrder = writeOrder

                for (readOrder in byteOrders) {
                    ch.readByteOrder = readOrder

                    assertEquals(0, ch.availableForRead)
                    ch.writeShort(0x001f)
                    ch.flush()
                    if (writeOrder == readOrder)
                        assertEquals(0x001f, ch.readShort())
                    else
                        assertEquals(0x1f00, ch.readShort())

                    assertEquals(0, ch.availableForRead)
                    ch.writeShort(0x001f)
                    ch.flush()
                    if (writeOrder == readOrder)
                        assertEquals(0x001f, ch.readShort())
                    else
                        assertEquals(0x1f00, ch.readShort())

                    assertEquals(0, ch.availableForRead)
                    ch.writeInt(0x1f)
                    ch.flush()
                    if (writeOrder == readOrder)
                        assertEquals(0x0000001f, ch.readInt())
                    else
                        assertEquals(0x1f000000, ch.readInt())

                    assertEquals(0, ch.availableForRead)
                    ch.writeInt(0x1fL)
                    ch.flush()
                    if (writeOrder == readOrder)
                        assertEquals(0x0000001f, ch.readInt())
                    else
                        assertEquals(0x1f000000, ch.readInt())

                    assertEquals(0, ch.availableForRead)
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
            assertEquals(5, ch.availableForRead)
            ch.readFully(dst)
            assertTrue { dst.contentEquals(bytes) }

            ch.writeFully(bytes)
            ch.flush()

            val dst2 = ByteArray(4)
            ch.readFully(dst2)

            assertEquals(1, ch.availableForRead)
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
            assertEquals(5, ch.availableForRead)
            ch.readFully(ByteBuffer.wrap(dst))
            assertTrue { dst.contentEquals(bytes) }

            ch.writeFully(ByteBuffer.wrap(bytes))
            ch.flush()

            val dst2 = ByteArray(4)
            ch.readFully(ByteBuffer.wrap(dst2))

            assertEquals(1, ch.availableForRead)
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

            assertEquals(5, ch.writeAvailable(bytes))
            ch.flush()
            assertEquals(5, ch.readAvailable(ByteArray(100)))

            repeat(Size / bytes.size) {
                assertNotEquals(0, ch.writeAvailable(bytes))
                ch.flush()
            }

            ch.readAvailable(ByteArray(ch.availableForRead - 1))
            assertEquals(1, ch.readAvailable(ByteArray(100)))

            ch.close()
        }
    }

    @Test
    fun testReadAndWritePartiallyByteBuffer() {
        runBlocking {
            val bytes = byteArrayOf(1, 2, 3, 4, 5)

            assertEquals(5, ch.writeAvailable(ByteBuffer.wrap(bytes)))
            ch.flush()
            assertEquals(5, ch.readAvailable(ByteBuffer.allocate(100)))

            repeat(Size / bytes.size) {
                assertNotEquals(0, ch.writeAvailable(ByteBuffer.wrap(bytes)))
                ch.flush()
            }

            ch.readAvailable(ByteArray(ch.availableForRead - 1))
            assertEquals(1, ch.readAvailable(ByteBuffer.allocate(100)))

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
            writeStringUtf8("Hello")
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
    fun testPacketMultipleBufferOfOne() = runBlocking {
        val packet0 = buildPacket {
            writeInt(0xffee)
            writeStringUtf8("Hello")
        } as ByteReadPacketViewBased

        val packet = ByteReadPacketViewBased(packet0.steal()!!)

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
                writeStringUtf8(".".repeat(8192))
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

    @Test
    fun testWriteString() = runBlocking {
        ch.writeStringUtf8("abc")
        ch.close()

        assertEquals("abc", ch.readASCIILine())
    }

    @Test
    fun testWriteCharSequence() = runBlocking {
        ch.writeStringUtf8("abc" as CharSequence)
        ch.close()

        assertEquals("abc", ch.readASCIILine())
    }

    @Test
    fun testWriteCharBuffer() = runBlocking {
        val cb = CharBuffer.allocate(6)

        for (i in 0 until cb.remaining()) {
            cb.put(i, ' ')
        }

        cb.position(2)
        cb.put(2, 'a')
        cb.put(3, 'b')
        cb.put(4, 'c')
        cb.limit(5)

        assertEquals("abc", cb.slice().toString())

        ch.writeStringUtf8(cb)
        ch.close()

        assertEquals("abc", ch.readASCIILine())
    }

    private inline fun buildPacket(block: ByteWritePacket.() -> Unit) = buildPacket(pktPool, 0, block)
}