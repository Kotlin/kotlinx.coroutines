package chat

import kotlinx.coroutines.channels.Channel

class UserWithFriends(id: Long,
                      sendingMessageSpeed : Double,
                      messagesChannel: Channel<Message>,
                      configuration: BenchmarkConfiguration,
                      shouldCountMetrics : Boolean)
    : User(id, sendingMessageSpeed, messagesChannel, configuration, shouldCountMetrics) {
    private lateinit var friends : List<Channel<Message>>

    fun setFriends(friends : List<Channel<Message>>) {
        this.friends = friends
    }

    override fun chooseChannelToSend(): Channel<Message> {
        val friendNum = random.nextInt(friends.size)
        return friends[friendNum]
    }
}