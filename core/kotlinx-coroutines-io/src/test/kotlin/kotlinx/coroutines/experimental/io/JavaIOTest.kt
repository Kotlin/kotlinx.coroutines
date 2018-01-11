package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.io.jvm.javaio.*
import kotlinx.coroutines.experimental.io.jvm.nio.*
import org.junit.Test
import java.io.*
import java.nio.channels.*
import kotlin.test.*

class JavaIOTest : TestBase() {
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
        val exec = newFixedThreadPoolContext(2, "blocking-io")

        val channel1 = ByteChannel(autoFlush = false)
        val channel2 = ByteChannel(autoFlush = false)

        val j1 = launch(exec) {
            try {
                channel1.copyTo(pipe)
            } finally {
                pipe.sink().close()
            }
        }

        j1.invokeOnCompletion {
            it?.let { println("j1 failed with $it"); it.printStackTrace() }
        }

        val j2 = launch(exec) {
            pipe.copyTo(channel2)
            channel2.close()
        }

        j2.invokeOnCompletion {
            it?.let { println("j2 failed with $it"); it.printStackTrace() }
        }

        channel1.writeStringUtf8("OK\n")
        channel1.close()

        try {
            assertEquals("OK", channel2.readUTF8Line())
        } catch (t: Throwable) {
            t.printStackTrace()
            j1.cancel()
            j2.cancel()
            channel1.close(t)
            channel2.close(t)
            throw t
        }

        j1.join()
        j2.join()


        exec.close()
    }

    @Test
    fun testPipedALot() = runBlocking {
        val exec = newFixedThreadPoolContext(2, "blocking-io")
        val numberOfLines = 10000
        val pipe = Pipe.open()

        val channel1 = ByteChannel()
        val channel2 = ByteChannel()

        launch(exec, parent = coroutineContext[Job]!!) {
            try {
                channel1.copyTo(pipe)
            } finally {
                pipe.sink().close()
            }
        }

        launch(exec, parent = coroutineContext[Job]!!) {
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

        exec.close()
    }

    @Test
    fun testPipedLimited() = runBlocking {
        val exec = newFixedThreadPoolContext(2, "blocking-io")
        val pipe = Pipe.open()

        val channel1 = ByteChannel()
        val channel2 = ByteChannel()

        launch(exec, parent = coroutineContext[Job]!!) {
            channel1.copyTo(pipe, limit = 1)
        }

        launch(exec, parent = coroutineContext[Job]!!) {
            pipe.copyTo(channel2, limit = 1)
            channel2.close()
        }

        channel1.writeStringUtf8("OK")
        channel1.close()

        assertEquals("O", channel2.readUTF8Line())

        pipe.source().close()
        pipe.sink().close()
        exec.close()
    }
}