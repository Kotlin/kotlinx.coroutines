package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.io.jvm.javaio.*
import kotlinx.coroutines.experimental.io.jvm.nio.*
import org.junit.Test
import java.io.*
import java.nio.channels.*
import kotlin.test.*

class JavaIOTest {
    private val channel = ByteChannel()

    @Test
    fun writeStream() = runBlocking {
        channel.writeStringUtf8("OK")
        channel.close()

        val baos = ByteArrayOutputStream()
        channel.copyTo(baos)

        assertEquals("OK", baos.toByteArray().toString(Charsets.ISO_8859_1))
    }

    @Test
    fun testReadStream() = runBlocking {
        val stream = ByteArrayInputStream("OK".toByteArray())
        stream.copyTo(channel)
        channel.close()

        assertEquals("OK", channel.readUTF8Line())
    }

    @Test
    fun testNIOWriteChannel() = runBlocking {
        val baos = ByteArrayOutputStream()
        val nioChannel = Channels.newChannel(baos)

        channel.writeStringUtf8("OK")
        channel.close()
        channel.copyTo(nioChannel)

        assertEquals("OK", baos.toByteArray().toString(Charsets.ISO_8859_1))
    }

    @Test
    fun testNIOReadChannel() = runBlocking {
        val nioChannel = Channels.newChannel(ByteArrayInputStream("OK".toByteArray()))

        nioChannel.copyTo(channel)
        channel.close()

        assertEquals("OK", channel.readUTF8Line())
    }

    @Test
    fun writeStreamLimit() = runBlocking {
        channel.writeStringUtf8("OK")
        channel.close()

        val baos = ByteArrayOutputStream()
        channel.copyTo(baos, limit = 1)

        assertEquals("O", baos.toByteArray().toString(Charsets.ISO_8859_1))
    }

    @Test
    fun testReadStreamLimit() = runBlocking {
        val stream = ByteArrayInputStream("OK".toByteArray())
        stream.copyTo(channel, limit = 1)
        channel.close()

        assertEquals("O", channel.readUTF8Line())
    }

    @Test
    fun testNIOWriteChannelLimit() = runBlocking {
        val baos = ByteArrayOutputStream()
        val nioChannel = Channels.newChannel(baos)

        channel.writeStringUtf8("OK")
        channel.close()
        channel.copyTo(nioChannel, limit = 1)

        assertEquals("O", baos.toByteArray().toString(Charsets.ISO_8859_1))
    }

    @Test
    fun testNIOReadChannelLimit() = runBlocking {
        val nioChannel = Channels.newChannel(ByteArrayInputStream("OK".toByteArray()))

        nioChannel.copyTo(channel, limit = 1)
        channel.close()

        assertEquals("O", channel.readUTF8Line())
    }

    @Test
    fun testPiped() = runBlocking {
        val pipe = Pipe.open()

        val channel1 = ByteChannel()
        val channel2 = ByteChannel()

        launch {
            try {
                channel1.copyTo(pipe)
            } finally {
                pipe.sink().close()
            }
        }

        launch {
            pipe.copyTo(channel2)
            channel2.close()
        }

        channel1.writeStringUtf8("OK")
        channel1.close()

        assertEquals("OK", channel2.readUTF8Line())
    }

    @Test
    fun testPipedALot() = runBlocking {
        val numberOfLines = 10000
        val pipe = Pipe.open()

        val channel1 = ByteChannel()
        val channel2 = ByteChannel()

        launch {
            try {
                channel1.copyTo(pipe)
            } finally {
                pipe.sink().close()
            }
        }

        launch {
            pipe.copyTo(channel2)
            channel2.close()
        }

        launch(coroutineContext) {
            for (i in 1..numberOfLines) {
                channel1.writeStringUtf8("OK $i\n")
            }
            channel1.close()
        }

        for (i in 1..numberOfLines) {
            assertEquals("OK $i", channel2.readUTF8Line())
        }
    }

    @Test
    fun testPipedLimited() = runBlocking {
        val pipe = Pipe.open()

        val channel1 = ByteChannel()
        val channel2 = ByteChannel()

        launch {
            channel1.copyTo(pipe, limit = 1)
        }

        launch {
            pipe.copyTo(channel2, limit = 1)
            channel2.close()
        }

        channel1.writeStringUtf8("OK")
        channel1.close()

        assertEquals("O", channel2.readUTF8Line())

        pipe.source().close()
        pipe.sink().close()
    }
}