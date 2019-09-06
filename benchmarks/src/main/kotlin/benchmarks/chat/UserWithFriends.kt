package benchmarks.chat

import kotlinx.coroutines.channels.Channel

class UserWithFriends(id: Long,
                      activity : Double,
                      messageChannel: Channel<Message>,
                      averageWork: Int)
    : User(id, activity, messageChannel, averageWork) {
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