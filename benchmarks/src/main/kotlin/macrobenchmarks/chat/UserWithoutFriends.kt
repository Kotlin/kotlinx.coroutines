/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package macrobenchmarks.chat

import kotlinx.coroutines.channels.Channel

class UserWithoutFriends(id: Long,
                         activity: Double,
                         messageChannel: Channel<Message>,
                         averageWork: Int)
    : User(id, activity, messageChannel, averageWork) {

    private lateinit var users: List<User>

    private lateinit var cumSumFriends : List<Double>

    fun setUsers(users : List<User>, cumSumFriends : List<Double>) {
        this.users = users
        this.cumSumFriends = cumSumFriends
    }

    override fun chooseUserToSend(): User {
        var user : User = this
        while (this == user) {
            val randomDouble = random.nextDouble() * cumSumFriends.last()
            var insertionPoint = cumSumFriends.binarySearch(randomDouble)

            // binary search can return negative values. It indicates the position in the original collection where
            // the searched element can be inserted
            if (insertionPoint < 0) insertionPoint = -(insertionPoint + 1)

            // insertionPoint won't be out of bounds because randomDouble is less than or equals to the last number in the
            // cumSumFriends list
            user =  users[insertionPoint]
        }
        return user
    }
}