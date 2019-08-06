package chat

import java.util.concurrent.atomic.AtomicLong

class Server(private val configuration: BenchmarkConfiguration) {
    private var idSequence = AtomicLong()

    fun registerClient(shouldCountMetrics : Boolean, sendingMessageSpeed : Double): User {
        val userId = idSequence.incrementAndGet()
        val messagesChannel = configuration.channelType.createChannel<Message>()

        return when (configuration.benchmarkMode) {
            BenchmarkModes.USER_WITH_FRIENDS -> UserWithFriends(userId, sendingMessageSpeed, messagesChannel, configuration, shouldCountMetrics)
            BenchmarkModes.USER_WITHOUT_FRIENDS -> UserWithoutFriends(userId, sendingMessageSpeed, messagesChannel, configuration, shouldCountMetrics)
        }
    }
}