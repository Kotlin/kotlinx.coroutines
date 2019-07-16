package inmemorychat

import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.launch
import kotlinx.coroutines.selects.select
import kotlinx.coroutines.yield

/**
 * An implementation of server-side users.
 * This implementation contains one coroutine which gets messages from messagesChannel, gets commands from commandsChannel,
 * and process them. User has two channels, and listens to both of them using select clause. If user gets the [SendMessage]
 * command, user sends a message to one of the friends chosen randomly. After receiving a [UserMessage],
 * user process it using [receiveAndProcessMessage].
 * Because of the design of the coroutines tasks scheduler and channels, it is important to call [yield] sometimes to allow other
 * coroutines to work. This is necessary due to the fact that if a coroutine constantly has some work to do, like in this
 * case if a coroutine has an endless flow of messages, it will work without interruption, and other coroutines will have to
 * wait for this coroutine to end it's execution.
 */
class UserWithSelect(
        id: Long,
        messagesChannel: Channel<Message>,
        val commandsChannel: Channel<Message>,
        properties: BenchmarkProperties,
        shouldCountMetrics: Boolean
) : User(id, messagesChannel, properties, shouldCountMetrics) {
    @Volatile
    private var stopped = false

    init {
        CoroutineScope(context).launch {
            var count = 0L
            while (!stopped) {
                select<Unit> {
                    messagesChannel.onReceiveOrNull {
                        if (it != null) {
                            receiveAndProcessMessage(it)
                        }
                    }
                    commandsChannel.onReceiveOrNull {
                        if (it != null) {
                            sendMessage()
                        }
                    }
                }
                if (count++ % 61 == 19L) {
                    yield()
                }
            }
        }
    }

    override fun stopUser() {
        stopped = true
        messagesChannel.close()
        commandsChannel.close()
    }
}