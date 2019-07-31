package chat

import kotlinx.coroutines.channels.Channel

class UserWithoutFriends(id: Long,
                         sendingMessageSpeed: Double,
                         messagesChannel: Channel<Message>,
                         configuration: BenchmarkConfiguration,
                         shouldCountMetrics: Boolean)
    : User(id, sendingMessageSpeed, messagesChannel, configuration, shouldCountMetrics) {

    private lateinit var users: List<User>

    private lateinit var cumSumFriends : List<Double>

    fun setUsers(users : List<User>, cumSumFriends : List<Double>) {
        this.users = users
        this.cumSumFriends = cumSumFriends
    }

    override fun chooseChannelToSend(): Channel<Message>? {
        var userId = id
        var user : User? = null
        while (id == userId) {
            val randomDouble = random.nextDouble() * cumSumFriends.last()
            var insertionPoint = cumSumFriends.binarySearch(randomDouble)

            // binary search can return negative values. It indicates the position in the original collection where
            // the searched element can be inserted
            if (insertionPoint < 0) {
                insertionPoint = -(insertionPoint + 1)
            }

            // insertionPoint won't be out of bounds because randomDouble is less than or equals to the last number in the
            // cumSumFriends list
            user =  users[insertionPoint]
            userId = user.id
        }
        return user?.messagesChannel
    }
}