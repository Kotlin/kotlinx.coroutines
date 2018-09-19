/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.examples

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.nio.*
import java.net.*
import java.nio.*
import java.nio.channels.*

val PORT = 12345
val CLIENT_READ_TIMEOUT = 5000L // 5 sec
val CLIENT_WRITE_TIMEOUT = 1000L // 1 sec
val BUFFER_SIZE = 1024

fun main(args: Array<String>) = runBlocking {
    val serverChannel =
        AsynchronousServerSocketChannel
            .open()
            .bind(InetSocketAddress(PORT))
    log("Listening on port $PORT")
    // loop and accept connections forever
    while (true) {
        val client = serverChannel.aAccept()
        val address = try {
            val ia = client.remoteAddress as InetSocketAddress
            "${ia.address.hostAddress}:${ia.port}"
        } catch (ex: Throwable) {
            log("Accepted client connection but failed to get its address because of $ex")
            continue /* accept next connection */
        }
        log("Accepted client connection from $address")
        // just start a new coroutine for each client connection
        launch {
            try {
                handleClient(client)
                log("Client connection from $address has terminated normally")
            } catch (ex: Throwable) {
                log("Client connection from $address has terminated because of $ex")
            }
        }
    }
}

suspend fun handleClient(client: AsynchronousSocketChannel) {
    val buffer = ByteBuffer.allocate(BUFFER_SIZE)
    while (true) {
        val bytes = withTimeout(CLIENT_READ_TIMEOUT) { client.aRead(buffer) }
        if (bytes < 0) break
        buffer.flip()
        withTimeout(CLIENT_WRITE_TIMEOUT) { client.aWrite(buffer) }
        buffer.clear()
    }
}

