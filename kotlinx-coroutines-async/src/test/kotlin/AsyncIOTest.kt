package kotlinx.coroutines.asyncIO

import kotlinx.coroutines.*
import org.apache.commons.io.FileUtils
import org.junit.Rule
import org.junit.Test
import org.junit.rules.TemporaryFolder
import java.net.InetSocketAddress
import java.nio.ByteBuffer
import java.nio.channels.AsynchronousFileChannel
import java.nio.channels.AsynchronousServerSocketChannel
import java.nio.channels.AsynchronousSocketChannel
import java.nio.file.StandardOpenOption
import java.util.concurrent.Executors
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class AsyncIOTest {
    @Rule
    @JvmField
    val tmpDir = TemporaryFolder()

    @Test
    fun testFileChannels() {
        val inputFile = tmpDir.newFile()
        val outputFile = tmpDir.newFile()

        FileUtils.writeStringToFile(
                inputFile,
                (1..100000).map(Int::toString).joinToString(""))

        val input = AsynchronousFileChannel.open(inputFile.toPath())
        val output =
                AsynchronousFileChannel.open(
                        outputFile.toPath(),
                        StandardOpenOption.CREATE, StandardOpenOption.WRITE)
        val buf = ByteBuffer.allocate(1024)
        val future = async {
            var totalBytesRead = 0L
            var totalBytesWritten = 0L
            while (totalBytesRead < input.size()) {
                while (buf.hasRemaining() && totalBytesRead < input.size()) {
                    // async read
                    totalBytesRead += input.aRead(buf, totalBytesRead)
                }

                buf.flip()

                while (buf.hasRemaining()) {
                    // async write
                    totalBytesWritten += output.aWrite(buf, totalBytesWritten)
                }

                buf.clear()
            }
        }

        assertEquals(Unit, future.get())
        assertTrue(FileUtils.contentEquals(inputFile, outputFile))
    }

    @Test
    fun testNetworkChannels() {
        val threadPool = Executors.newFixedThreadPool(1)
        val serverChannel =
                AsynchronousServerSocketChannel
                        .open()
                        .bind(InetSocketAddress(8080))

        threadPool.submit {
            async {
                val client = serverChannel.aAccept()
                val buffer = ByteBuffer.allocate(2)
                client.aRead(buffer)

                assertEquals("OK", Charsets.UTF_8.decode(buffer).toString())

                client.aWrite(Charsets.UTF_8.encode("123"))
                client.close()
            }
        }

        async {
            val connection =
                    AsynchronousSocketChannel.open()
            // async calls
            connection.aConnect(InetSocketAddress("127.0.0.1", 8080))
            connection.aWrite(Charsets.UTF_8.encode("OK"))

            val buffer = ByteBuffer.allocate(3)

            // async call
            connection.aRead(buffer)

            assertEquals("123", Charsets.UTF_8.decode(buffer).toString())
        }

        threadPool.shutdown()
    }
}
