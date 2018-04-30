package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.CancellationException
import kotlinx.coroutines.experimental.channels.*
import kotlinx.coroutines.experimental.io.internal.*
import kotlinx.coroutines.experimental.io.packet.*
import kotlinx.coroutines.experimental.io.packet.ByteReadPacket
import kotlinx.io.core.*
import kotlinx.io.pool.*
import org.junit.*
import org.junit.Test
import org.junit.rules.*
import java.nio.CharBuffer
import java.util.*
import java.util.concurrent.*
import java.util.concurrent.atomic.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

class ByteBufferChannelTest : TestBase() {
    @get:Rule
    val timeout = Timeout(100L * stressTestMultiplier, TimeUnit.SECONDS)

    @get:Rule
    private val failures = ErrorCollector()

    @get:Rule
    internal val pool = VerifyingObjectPool(object : NoPoolImpl<ReadWriteBufferState.Initial>() {
        override fun borrow(): ReadWriteBufferState.Initial {
            return ReadWriteBufferState.Initial(java.nio.ByteBuffer.allocate(4096))
        }
    })

    @get:Rule
    internal val pktPool = VerifyingObjectPool(BufferView.Pool)

    private val Size = BUFFER_SIZE - RESERVED_SIZE
    private val ch = ByteBufferChannel(autoFlush = false, pool = pool)

    @After
    fun finish() {
        ch.close(InterruptedException())
    }

    @Test
    fun testBoolean() {
        runTest {
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
        runTest {
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
        runTest {
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
        runTest {
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
        runTest {
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
        runTest {
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
        runTest {
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
        runTest {
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
        runTest {
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
        runTest {
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
        runTest {
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
        runTest {
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
        runTest {
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
        runTest {
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
        runTest {
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
        runTest {
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
        runTest {
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
        runTest {
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
        runTest {
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
        runTest {
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
        runTest {
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

        runTest {
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

        runTest {
            val dst = ByteArray(bytes.size)
            for (i in 1..count) {
                ch.readFully(ByteBuffer.wrap(dst))
                assertTrue { dst.contentEquals(bytes) }
                dst.fill(0)
            }
        }
    }

    @Test
    fun testPacket() = runTest {
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
    fun testBigPacket() = runTest {
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
    fun testWriteString() = runTest {
        ch.writeStringUtf8("abc")
        ch.close()

        assertEquals("abc", ch.readASCIILine())
    }

    @Test
    fun testWriteCharSequence() = runTest {
        ch.writeStringUtf8("abc" as CharSequence)
        ch.close()

        assertEquals("abc", ch.readASCIILine())
    }

    @Test
    fun testWriteCharBuffer() = runTest {
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

    @Test
    fun testReadAndWriteLarge() = runTest {
        val count = 128L * 1024 * stressTestMultiplier // * 8192 -> 1G * M
        val data = ByteBuffer.allocate(8192)!!
        Random().nextBytes(data.array())

        launch("writer") {
            repeat(count.toInt()) {
                data.clear()
                ch.writeFully(data)
            }
            ch.close()
        }

        launch("reader") {
            val buffer = ByteBuffer.allocate(8192)!!
            var read = 0L
            val total = count * 8192

            while (read < total) {
                buffer.clear()
                val rc = ch.readFully(buffer)
                if (rc == -1) break
                read += rc
            }

            assertEquals(total, read)

            buffer.clear()
            assertEquals(-1, ch.readAvailable(buffer))
        }
    }

    @Test
    fun testReadAndWriteLargeViaLookAheadSession() = runTest {
        val count = 128L * 1024 * stressTestMultiplier // * 8192 -> 1G * M
        val data = ByteBuffer.allocate(8192)!!
        Random().nextBytes(data.array())

        launch("writer") {
            repeat(count.toInt()) {
                data.clear()
                ch.writeFully(data)
            }
            ch.close()
        }

        launch("reader") {
            var read = 0L
            val total = count * 8192

            ch.lookAheadSuspend {
                while (read < total) {
                    val bb = request(0, 1)
                    if (bb == null) {
                        if (!awaitAtLeast(1)) break
                        continue
                    }
                    val rc = bb.remaining()
                    bb.position(bb.limit())
                    read += rc
                    consumed(rc)
                }
            }

            assertEquals(total, read)
            assertEquals(-1, ch.readAvailable(ByteBuffer.allocate(8192)))
        }
    }

    @Test
    fun testCopyLarge() {
        val count = 100 * 256 * stressTestMultiplier // * 8192

        launch {
            val bb = ByteBuffer.allocate(8192)
            for (i in 0 until bb.capacity()) {
                bb.put((i and 0xff).toByte())
            }

            for (i in 1..count) {
                bb.clear()
                val split = i and 0x1fff

                bb.limit(split)
                ch.writeFully(bb)
                yield()
                bb.limit(bb.capacity())
                ch.writeFully(bb)
            }

            ch.close()
        }

        val dest = ByteBufferChannel(true, pool)

        val joinerJob = launch {
            ch.copyAndClose(dest)
        }

        val reader = launch {
            val bb = ByteBuffer.allocate(8192)

            for (i in 1..count) {
                bb.clear()
                dest.readFully(bb)
                bb.flip()

                if (i and 0x1fff == 0) {
                    for (idx in 0 until bb.capacity()) {
                        assertEquals((idx and 0xff).toByte(), bb.get())
                    }
                }
            }

            yield()
            assertTrue(dest.isClosedForRead)
        }

        runTest {
            reader.join()
            joinerJob.join()
            dest.close()
            ch.close()
        }
    }

    @Test
    fun testJoinToLarge() {
        val count = 100 * 256 * stressTestMultiplier // * 8192

        val writerJob = launch {
            val bb = ByteBuffer.allocate(8192)
            for (i in 0 until bb.capacity()) {
                bb.put((i and 0xff).toByte())
            }

            for (i in 1..count) {
                bb.clear()
                val split = i and 0x1fff

                bb.limit(split)
                ch.writeFully(bb)
                yield()
                bb.limit(bb.capacity())
                ch.writeFully(bb)
            }

            ch.close()
        }

        val dest = ByteBufferChannel(true, pool)

        val joinerJob = launch {
            ch.joinTo(dest, true)
        }

        val reader = launch {
            val bb = ByteBuffer.allocate(8192)

            for (i in 1..count) {
                bb.clear()
                dest.readFully(bb)
                bb.flip()

                if (i and 0x1fff == 0) {
                    for (idx in 0 until bb.capacity()) {
                        assertEquals((idx and 0xff).toByte(), bb.get())
                    }
                }
            }

            bb.clear()
            assertEquals(-1, dest.readAvailable(bb))
            assertTrue(dest.isClosedForRead)
        }

        val latch = CountDownLatch(1)
        val r = AtomicInteger(3)

        val handler: CompletionHandler = { t ->
            t?.let { failures.addError(it); latch.countDown() }
            if (r.decrementAndGet() == 0) latch.countDown()
        }

        reader.invokeOnCompletion(onCancelling = true, handler = handler)
        writerJob.invokeOnCompletion(onCancelling = true, handler = handler)
        joinerJob.invokeOnCompletion(onCancelling = true, handler = handler)

        latch.await()
    }

    private suspend fun launch(name: String = "child", block: suspend () -> Unit): Job {
        return launch(context = DefaultDispatcher + CoroutineName(name), parent = coroutineContext[Job]) {
            block()
        }.apply {
            invokeOnCompletion( onCancelling = true) { t ->
                if (t != null) ch.cancel(t)
            }
        }
    }

    private fun launch(block: suspend () -> Unit): Job {
        return launch(DefaultDispatcher) {
            try {
                block()
            } catch (t: Throwable) {
                failures.addError(t)
            }
        }
    }

    @Test
    fun testStressReadWriteFully() = runTest {
        val size = 100
        val data = ByteArray(size) { it.toByte() }
        val exec = newFixedThreadPoolContext(8, "testStressReadFully")
        val buffers = object : DefaultPool<ByteArray>(10) {
            override fun produceInstance(): ByteArray {
                return ByteArray(size)
            }
        }

        try {
            (1..100_000 * stressTestMultiplier).map {
                async(exec) {
                    val channel = ByteBufferChannel(autoFlush = false, pool = pool)
                    val job = launch(exec) {
                        try {
                            channel.writeFully(data)
                        } finally {
                            channel.close()
                        }
                    }

                    yield()
                    val buffer = buffers.borrow()
                    channel.readFully(buffer)
                    buffers.recycle(buffer)
                    job.cancel()
                }
            }.forEach {
                it.await()
            }
        } finally {
            exec.close()
        }
    }

    @Test
    fun testJoinToSmokeTest() = runTest {
        val other = ByteBufferChannel(autoFlush = false, pool = pool)
        launch(coroutineContext) {
            ch.joinTo(other, false)
        }
        yield()

        ch.writeInt(0x11223344)
        ch.flush()
        assertEquals(0x11223344, other.readInt())

        ch.close()
    }

    @Test
    fun testJoinToChainSmokeTest1() = runTest {
        val A = ByteBufferChannel(autoFlush = false, pool = pool)
        val B = ByteBufferChannel(autoFlush = false, pool = pool)
        val C = ByteBufferChannel(autoFlush = false, pool = pool)

        launch(coroutineContext) {
            B.joinTo(C, closeOnEnd = true)
        }
        launch(coroutineContext) {
            A.joinTo(B, closeOnEnd = true)
        }

        yield()
        A.writeStringUtf8("OK")
        A.close()

        assertEquals("OK", C.readUTF8Line())
    }

    @Test
    fun testJoinToChainSmokeTest2() = runTest {
        val A = ByteBufferChannel(autoFlush = false, pool = pool)
        val B = ByteBufferChannel(autoFlush = false, pool = pool)
        val C = ByteBufferChannel(autoFlush = false, pool = pool)

        launch(coroutineContext) {
            A.joinTo(B, closeOnEnd = true)
        }
        launch(coroutineContext) {
            B.joinTo(C, closeOnEnd = true)
        }

        yield()
        A.writeStringUtf8("OK")
        A.close()

        assertEquals("OK", C.readUTF8Line())
    }

    @Test
    fun testJoinToChainSmokeTest3() = runTest {
        val A = ByteBufferChannel(autoFlush = false, pool = pool)
        val B = ByteBufferChannel(autoFlush = false, pool = pool)
        val C = ByteBufferChannel(autoFlush = false, pool = pool)

        launch(coroutineContext + CoroutineName("A->B")) {
            A.joinTo(B, closeOnEnd = true)
        }
        launch(coroutineContext + CoroutineName("B->C")) {
            B.joinTo(C, closeOnEnd = true)
        }

        A.writeStringUtf8("OK\n")
//        A.close()
        A.flush()
        yield()
        yield()
        yield()
        A.close()

        assertEquals("OK", C.readUTF8Line())
    }

    @Test
    fun testJoinToChainSmokeTest4() = runTest {
        val A = ByteBufferChannel(autoFlush = false, pool = pool)
        val B = ByteBufferChannel(autoFlush = false, pool = pool)
        val C = ByteBufferChannel(autoFlush = false, pool = pool)

        launch(coroutineContext + CoroutineName("A->B")) {
            A.joinTo(B, closeOnEnd = true)
        }
        launch(coroutineContext + CoroutineName("B->C")) {
            B.joinTo(C, closeOnEnd = true)
        }

        A.writeStringUtf8("OK\n")
        A.close()

        assertEquals("OK", C.readUTF8Line())
    }

    @Test
    fun testJoinToFull() = runTest() {
        val D = ByteBufferChannel(autoFlush = false, pool = pool)

        var written = 0
        D.writeByte(1)
        written++
        while (D.availableForWrite > 0) {
            D.writeByte(1)
            written++
        }

        ch.writeInt(777)
        ch.close()

        launch(coroutineContext) {
            ch.joinTo(D, true)
        }

        yield()

        repeat(written) {
            D.readByte()
        }

        assertEquals(777, D.readInt())
    }

    @Test
    fun testJoinToChainNonEmpty() = runTest {
        val A = ByteBufferChannel(autoFlush = false, pool = pool)
        val B = ByteBufferChannel(autoFlush = false, pool = pool)
        val C = ByteBufferChannel(autoFlush = false, pool = pool)

        A.writeStringUtf8("1")
        A.flush()

        launch(coroutineContext + CoroutineName("Reader")) {
            assertEquals("1OK", C.readUTF8Line())
        }
        yield()

        launch(coroutineContext + CoroutineName("A->B")) {
            A.joinTo(B, closeOnEnd = true)
        }

        yield()

        launch(coroutineContext + CoroutineName("B->C")) {
            B.joinTo(C, closeOnEnd = true)
        }
        yield()


        yield()
        yield()
        yield()

        A.writeStringUtf8("OK\n")
        A.close()
    }

    @Test
    fun testCopyToThenJoinTo() = runTest {
        val A = ByteBufferChannel(autoFlush = false, pool = pool)
        val B = ByteBufferChannel(autoFlush = false, pool = pool)
        val C = ByteBufferChannel(autoFlush = false, pool = pool)

//        A.writeStringUtf8("1")
//        A.flush()

        launch(coroutineContext + CoroutineName("A->B")) {
            A.copyAndClose(B)
        }

        launch(coroutineContext + CoroutineName("Reader")) {
            assertEquals("1OK", C.readUTF8Line())
        }

        launch(coroutineContext + CoroutineName("B->C")) {
            B.joinTo(C, closeOnEnd = true)
        }

        A.writeStringUtf8("1OK\n")
        A.close()
    }

    @Test
    fun testCopyToThenJoinTo2() = runTest {
        val A = ByteBufferChannel(autoFlush = false, pool = pool)
        val B = ByteBufferChannel(autoFlush = false, pool = pool)
        val C = ByteBufferChannel(autoFlush = false, pool = pool)

        A.writeStringUtf8("1")
        A.flush()

        launch(coroutineContext + CoroutineName("A->B")) {
            A.copyAndClose(B)
        }

        launch(coroutineContext + CoroutineName("Reader")) {
            assertEquals("1OK", C.readUTF8Line())
        }

        launch(coroutineContext + CoroutineName("B->C")) {
            B.joinTo(C, closeOnEnd = true)
        }

        A.writeStringUtf8("OK\n")
        A.close()
    }

    @Test
    fun testCopyToThenJoinTo3() = runTest {
        val A = ByteBufferChannel(autoFlush = false, pool = pool)
        val B = ByteBufferChannel(autoFlush = false, pool = pool)
        val C = ByteBufferChannel(autoFlush = false, pool = pool)

        A.writeStringUtf8("1")
        A.flush()

        launch(coroutineContext + CoroutineName("A->B")) {
            A.copyAndClose(B)
        }

        yield()

        launch(coroutineContext + CoroutineName("Reader")) {
            assertEquals("1OK", C.readUTF8Line())
        }

        launch(coroutineContext + CoroutineName("B->C")) {
            B.joinTo(C, closeOnEnd = true)
        }

        A.writeStringUtf8("OK\n")
        A.close()
    }

    @Test
    fun testCopyToThenJoinTo4() = runTest {
        val A = ByteBufferChannel(autoFlush = false, pool = pool)
        val B = ByteBufferChannel(autoFlush = false, pool = pool)
        val C = ByteBufferChannel(autoFlush = false, pool = pool)

        A.writeStringUtf8("1")
        A.flush()

        launch(coroutineContext + CoroutineName("Reader")) {
            assertEquals("1OK", C.readUTF8Line())
        }

        yield()

        launch(coroutineContext + CoroutineName("A->B")) {
            A.copyAndClose(B)
        }

        launch(coroutineContext + CoroutineName("B->C")) {
            B.joinTo(C, closeOnEnd = true)
        }

        A.writeStringUtf8("OK\n")
        A.close()
    }

    @Test
    fun testCopyToThenJoinTo5() = runTest {
        val A = ByteBufferChannel(autoFlush = false, pool = pool)
        val B = ByteBufferChannel(autoFlush = false, pool = pool)
        val C = ByteBufferChannel(autoFlush = false, pool = pool)

        A.writeStringUtf8("1")
        A.flush()

        launch(coroutineContext + CoroutineName("B->C")) {
            B.joinTo(C, closeOnEnd = true)
        }

        yield()

        launch(coroutineContext + CoroutineName("Reader")) {
            assertEquals("1OK", C.readUTF8Line())
        }
        yield()

        launch(coroutineContext + CoroutineName("A->B")) {
            A.copyAndClose(B)
        }

        A.writeStringUtf8("OK\n")
        A.close()
    }

    @Test
    fun testCopyToThenJoinTo6() = runTest {
        val A = ByteBufferChannel(autoFlush = false, pool = pool)
        val B = ByteBufferChannel(autoFlush = false, pool = pool)
        val C = ByteBufferChannel(autoFlush = false, pool = pool)

        A.writeStringUtf8("1")
        A.flush()

        launch(coroutineContext + CoroutineName("B->C")) {
            B.joinTo(C, closeOnEnd = true)
        }

        yield()
        launch(coroutineContext + CoroutineName("A->B")) {
            A.copyAndClose(B)
        }

        yield()

        launch(coroutineContext + CoroutineName("Reader")) {
            assertEquals("1OK", C.readUTF8Line())
        }

        A.writeStringUtf8("OK\n")
        A.close()
    }

    @Test
    fun testJoinClosed() = runTest {
        ch.writeInt(777)
        ch.close()

        val bc = ByteBufferChannel(autoFlush = false, pool = pool)
        ch.joinTo(bc, closeOnEnd = true)

        assertEquals(777, bc.readInt())
        assertEquals(0, bc.readRemaining().remaining)
    }

    @Test
    fun testJoinToResumeRead() = runTest {
        val other = ByteBufferChannel(autoFlush = true, pool = pool)
        val result = async(coroutineContext) {
            other.readLong()
        }
        yield()

        launch(coroutineContext) {
            ch.joinTo(other, true)
        }
        yield()
        yield()

        ch.writeLong(0x1122334455667788L)
        yield()
        assertEquals(0x1122334455667788L, result.await())

        ch.close()
    }

    @Test
    fun testJoinToAfterWrite() = runTest {
        val other = ByteBufferChannel(autoFlush = false, pool = pool)

        ch.writeInt(0x12345678)
        launch(coroutineContext) {
            ch.joinTo(other, false)
        }

        ch.writeInt(0x11223344)
        ch.flush()

        yield()

        assertEquals(0x12345678, other.readInt())
        assertEquals(0x11223344, other.readInt())
        ch.close()
    }

    @Test
    fun testJoinToClosed() = runTest {
        val other = ByteBufferChannel(autoFlush = false, pool = pool)

        ch.writeInt(0x11223344)
        ch.close()

        ch.joinTo(other, true)
        yield()

        assertEquals(0x11223344, other.readInt())
        assertTrue { other.isClosedForRead }
    }

    @Test
    fun testJoinToDifferentEndian() = runTest {
        val other = ByteBufferChannel(autoFlush = true, pool = pool)
        other.writeByteOrder = ByteOrder.LITTLE_ENDIAN
        ch.writeByteOrder = ByteOrder.BIG_ENDIAN

        ch.writeInt(0x11223344) // BE

        launch(coroutineContext) {
            ch.joinTo(other, true)
        }

        yield()

        ch.writeInt(0x55667788) // BE
        ch.writeByteOrder = ByteOrder.LITTLE_ENDIAN
        ch.writeInt(0x0abbccdd) // LE
        ch.close()

        other.readByteOrder = ByteOrder.BIG_ENDIAN
        assertEquals(0x11223344, other.readInt()) // BE
        assertEquals(0x55667788, other.readInt()) // BE
        other.readByteOrder = ByteOrder.LITTLE_ENDIAN
        assertEquals(0x0abbccdd, other.readInt()) // LE
    }

    @Test
    fun testReadThenRead() = runTest {
        val phase = AtomicInteger(0)

        val first = launch(coroutineContext) {
            try {
                ch.readInt()
                fail("EOF expected")
            } catch (expected: ClosedReceiveChannelException) {
                assertEquals(1, phase.get())
            }
        }

        yield()

        val second = launch(coroutineContext) {
            try {
                ch.readInt()
                fail("Should fail with ISE")
            } catch (expected: IllegalStateException) {
            }
        }

        yield()
        phase.set(1)
        ch.close()

        yield()

        first.invokeOnCompletion { t ->
            t?.let { throw it }
        }
        second.invokeOnCompletion { t ->
            t?.let { throw it }
        }
    }

    @Test
    fun writeThenReadStress() = runTest {
        ch.close()

        for (i in 1..50_000 * stressTestMultiplier) {
            val a = ByteBufferChannel(false, pool)

            val w = launch {
                a.writeLong(1)
                a.close()
            }
            val r = launch {
                a.readLong()
            }

            w.join()
            r.join()
        }
    }

    @Test
    fun joinToEmptyStress() = runTest {
        for (i in 1..50_000 * stressTestMultiplier) {
            val a = ByteBufferChannel(false, pool)

            launch(coroutineContext) {
                a.joinTo(ch, true)
            }

            yield()

            a.close()
        }
    }

    @Test
    fun testJoinToStress() = runTest {
        for (i in 1..10000 * stressTestMultiplier) {
            val child = ByteBufferChannel(false, pool)
            val writer = launch {
                child.writeLong(999 + i.toLong())
                child.close()
            }

            child.joinTo(ch, false)
            assertEquals(999 + i.toLong(), ch.readLong())
            writer.join()
        }

        assertEquals(0, ch.availableForRead)
        ch.close()
    }

    @Test
    fun testSequentialJoin() = runTest {
        val steps = 20_000 * stressTestMultiplier

        val pipeline = launch(coroutineContext) {
            for (i in 1..steps) {
                val child = ByteBufferChannel(false, pool)
                launch(coroutineContext) {
                    child.writeInt(i)
                    child.close()
                }
                child.joinTo(ch, false)
            }
        }

        for (i in 1..steps) {
            assertEquals(i, ch.readInt())
        }

        pipeline.join()
        pipeline.invokeOnCompletion { cause ->
            cause?.let { throw it }
        }
    }

    @Test
    fun testSequentialJoinYield() = runTest {
        val steps = 20_000 * stressTestMultiplier

        val pipeline = launch(coroutineContext) {
            for (i in 1..steps) {
                val child = ByteBufferChannel(false, pool)
                launch(coroutineContext) {
                    child.writeInt(i)
                    child.close()
                }
                yield()
                child.joinTo(ch, false)
            }
        }

        for (i in 1..steps) {
            assertEquals(i, ch.readInt())
        }

        pipeline.join()
        pipeline.invokeOnCompletion { cause ->
            cause?.let { throw it }
        }
    }

    @Test
    fun testJoinToNoFlush() = runTest {
        val src = ByteChannel(false)
        launch(coroutineContext) {
            src.joinTo(ch, closeOnEnd = false, flushOnEnd = false)
            assertEquals(0, ch.availableForRead)
            ch.flush()
            assertEquals(4, ch.availableForRead)
        }
        yield()

        src.writeInt(777)
        src.close()
    }

    @Test
    fun testReadBlock() = runTest {
        var bytesRead = 0L

        val r: (ByteBuffer) -> Unit = { bb ->
            bytesRead += bb.remaining()
            bb.position(bb.limit())
        }

        val j = launch(coroutineContext) {
            while (!ch.isClosedForRead) {
                ch.read(0, r)
            }
        }

        yield()

        ch.writeStringUtf8("OK\n")
        ch.close()

        j.join()
        j.invokeOnCompletion {
            it?.let { throw it }
        }
    }

    @Test
    fun testReadBlock2() = runTest {
        var bytesRead = 0L

        val r: (ByteBuffer) -> Unit = { bb ->
            bytesRead += bb.remaining()
            bb.position(bb.limit())
        }

        val j = launch(coroutineContext) {
            while (!ch.isClosedForRead) {
                ch.read(0, r)
            }
        }

        ch.writeStringUtf8("OK\n")
        yield()
        ch.close()

        j.join()
        j.invokeOnCompletion {
            it?.let { throw it }
        }
    }

    @Test
    fun testCancelWriter() = runTest {
        val sub = writer(DefaultDispatcher) {
            delay(1000000L)
        }

        sub.channel.cancel()
        sub.join()
    }

    @Test
    fun testCancelReader() = runTest {
        val sub = reader(DefaultDispatcher) {
            delay(10000000L)
        }

        sub.channel.close(CancellationException())
        sub.join()
    }

    private inline fun buildPacket(block: ByteWritePacket.() -> Unit): ByteReadPacket {
        val builder = BytePacketBuilder(0, pktPool)
        try {
            block(builder)
            return builder.build()
        } catch (t: Throwable) {
            builder.release()
            throw t
        }
    }
}