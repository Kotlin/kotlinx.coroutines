package inmemorychat

import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.channels.ClosedSendChannelException
import java.util.concurrent.ConcurrentHashMap

class Server(private val properties: BenchmarkProperties) {
    private var idSequence = 0L

    private val userIdToChannel = ConcurrentHashMap<Long, Channel<Message>>()

    fun registerClient(shouldCountMetrics : Boolean): User {
        val userId = idSequence++
        val messagesChannel = Channel<Message>(properties.channelType)
        userIdToChannel[userId] = messagesChannel

        return when (properties.userType) {
            UserType.USER_WITH_TWO_JOBS -> UserWithTwoJobs(this, userId, messagesChannel, properties, shouldCountMetrics)
            UserType.USER_WITH_ONE_JOB -> UserWithOneJob(this, userId, messagesChannel, properties, shouldCountMetrics)
            UserType.USER_WITH_SELECT -> UserWithSelect(this, userId, messagesChannel, Channel(properties.channelType),
                    properties, shouldCountMetrics)
        }
    }

    suspend fun sendMessage(userId: Long, message: Message) {
        try {
            userIdToChannel[userId]!!.send(message)
        }
        catch (ignored : ClosedSendChannelException) {}
    }
}