package inmemorychat

import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.launch
import kotlinx.coroutines.yield

/**
 * An implementation of server-side users.
 * This implementation contains one coroutine which gets messages from messagesChannel and process them. If user
 * gets the [SendMessage] command, user sends a message to one of the friends chosen randomly. After receiving
 * a [UserMessage], user process it using [receiveAndProcessMessage]
 * Because of the design of the coroutines tasks scheduler, it is important to call [yield] sometimes to allow other
 * coroutines to work. This is necessary due to the fact that if a coroutine constantly has some work to do, like in this
 * case if a coroutine has an endless flow of messages, it will work without interruption, and other coroutines will have to
 * wait for this coroutine to end it's execution.
 */
class UserWithOneJob(server: Server, id: Long, messagesChannel: Channel<Message>, properties: BenchmarkProperties,
                     shouldCountMetrics : Boolean)
    : User(server, id, messagesChannel, properties, shouldCountMetrics) {
    @Volatile
    private var stopped = false

    init {
        CoroutineScope(context).launch {
            var count = 0L
            for (message in messagesChannel) {
                if (stopped) {
                    break
                }
                when (message) {
                    is SendMessage -> {
                        sendMessage()
                    }
                    is UserMessage -> {
                        receiveAndProcessMessage(message)
                    }
                }
                if (count++ % 61 == 5L) {
                    yield()
                }
            }
        }
    }

    override fun stopUser() {
        stopped = true
        messagesChannel.close()
    }
}