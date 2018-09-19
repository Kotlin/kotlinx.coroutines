/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.nio

import kotlinx.coroutines.experimental.*
import org.apache.commons.io.*
import org.junit.*
import org.junit.Assert.*
import org.junit.rules.*
import java.net.*
import java.nio.*
import java.nio.channels.*
import java.nio.file.*

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

        runBlocking {
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

        assertTrue(FileUtils.contentEquals(inputFile, outputFile))
    }

    @Test
    fun testNetworkChannels() = runBlocking {
        val serverChannel =
                AsynchronousServerSocketChannel
                        .open()
                        .bind(InetSocketAddress(0))

        val serverPort = (serverChannel.localAddress as InetSocketAddress).port

        val c1 = launch {
            val client = serverChannel.aAccept()
            val buffer = ByteBuffer.allocate(2)
            client.aRead(buffer)
            buffer.flip()
            assertEquals("OK", Charsets.UTF_8.decode(buffer).toString())

            client.aWrite(Charsets.UTF_8.encode("123"))
            client.close()
        }

        val c2 = launch {
            val connection =
                    AsynchronousSocketChannel.open()
            // async calls
            connection.aConnect(InetSocketAddress("127.0.0.1", serverPort))
            connection.aWrite(Charsets.UTF_8.encode("OK"))

            val buffer = ByteBuffer.allocate(3)

            // async call
            connection.aRead(buffer)
            buffer.flip()
            assertEquals("123", Charsets.UTF_8.decode(buffer).toString())
        }

        c1.join()
        c2.join()
    }
}
