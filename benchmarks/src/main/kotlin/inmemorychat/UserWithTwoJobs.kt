package inmemorychat

import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.launch
import kotlinx.coroutines.yield

/**
 * An implementation of server-side users.
 * This implementation contains two coroutines. One of them generates flow of messages to random chosen user's friends.
 * The other one listens to messagesChannel and processes messages from other users using [receiveAndProcessMessage].
 * Because of the design of the coroutines tasks scheduler and channels, it is important to call [yield] sometimes to allow other
 * coroutines to work. This is necessary due to the fact that if a coroutine constantly has some work to do, like in this
 * case if a coroutine has an endless flow of messages, it will work without interruption, and other coroutines will have to
 * wait for this coroutine to end it's execution.
 */
class UserWithTwoJobs(id: Long, messagesChannel: Channel<Message>, properties: BenchmarkProperties,
                      shouldCountMetrics: Boolean) : User(id, messagesChannel, properties, shouldCountMetrics) {
    @Volatile
    private var stopped = false

    private var messageProbability = 1.0

    init {
        CoroutineScope(context).launch {
            var count = 0L
            while (!stopped) {
                // The more a user has friends, the more often the user sends messages to them. If a user has
                // properties.maxFriendsPercentage * properties.userCount friends, the user will send messages all the time
                val friendsPercentage = friends.size / properties.userCount.toDouble()
                messageProbability = friendsPercentage / properties.maxFriendsPercentage
                if (random.nextFloat() < messageProbability) {
                    sendMessage()
                }
                if (count++ % 61 == 31L) {
                    yield()
                }
            }
        }
        CoroutineScope(context).launch {
            var count = 0L
            for (message in messagesChannel) {
                if (stopped) {
                    break
                }
                receiveAndProcessMessage(message)
                if (count++ % 61 == 29L) {
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
