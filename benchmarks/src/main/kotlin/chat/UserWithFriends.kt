package chat

import kotlinx.coroutines.channels.Channel

class UserWithFriends(id: Long,
                      activity : Double,
                      messageChannel: Channel<Message>,
                      configuration: BenchmarkConfiguration)
    : User(id, activity, messageChannel, configuration) {
    private lateinit var friends : List<User>

    fun setFriends(friends : List<User>) {
        this.friends = friends
    }

    override fun chooseUserToSend(): User {
        var user : User = this
        while (user == this) {
            val friendNum = random.nextInt(friends.size)
            user =  friends[friendNum]
        }
        return user
    }
}