/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package examples

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.nio.*
import java.net.*
import java.nio.*
import java.nio.channels.*
import kotlin.coroutines.experimental.*

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
        launch(coroutineContext) {
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

