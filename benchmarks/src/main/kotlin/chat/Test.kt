@file:JvmName("Test")

package chat

import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.asCoroutineDispatcher
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.channels.ClosedSendChannelException
import kotlinx.coroutines.launch
import kotlinx.coroutines.selects.select
import java.util.concurrent.ForkJoinPool

var receivedMessages : Long = 0
var sentMessages : Long = 0

fun main() {
    val chan1 = Channel<Int>()
    val chan2 = Channel<Int>()

    val context = ForkJoinPool(1).asCoroutineDispatcher()

    CoroutineScope(context).launch {
        while (true) {
            sendMessage(chan1, chan2)
        }
    }

    CoroutineScope(context).launch {
        while (true) {
            sendMessage(chan2, chan1)
        }
    }

    Thread.sleep(1000)
    chan1.close()
    chan2.close()
    Thread.sleep(1000)
}

private suspend fun sendMessage(chanToReceive : Channel<Int>, chanToSend : Channel<Int>) {
    try {
        select<Unit> {
            chanToSend.onReceiveOrClosed { message ->
                run {
                    if (!message.isClosed) {
                        receivedMessages++
                    }
                }
            }
            chanToReceive.onSend(1) {
                sentMessages++
            }
        }
    } catch (ignored : ClosedSendChannelException) {}
}