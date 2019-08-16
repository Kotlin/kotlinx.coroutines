package chat

import kotlinx.coroutines.channels.Channel

class UserWithFriends(id: Long,
                      activity : Double,
                      messageChannel: Channel<Message>,
                      configuration: BenchmarkConfiguration)
    : User(id, activity, messageChannel, configuration) {
    private lateinit var friends : List<Channel<Message>>

    fun setFriends(friends : List<Channel<Message>>) {
        this.friends = friends
    }

    override fun chooseChannelToSend(): Channel<Message> {
        val friendNum = random.nextInt(friends.size)
        return friends[friendNum]
    }
}