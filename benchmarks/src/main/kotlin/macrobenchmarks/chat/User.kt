/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package macrobenchmarks.chat

import benchmarks.common.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.channels.koval_europar.*
import kotlinx.coroutines.selects.*
import java.util.*

/**
 * An abstract class for server-side chat users.
 * Every user has its own channel through which users can get messages from other users [receiveAndProcessMessage],
 * users can send messages to their friends' channels as well [sendMessage].
 * User contains sent and received messages metrics.
 * To emulate real world chat servers, some work will be executed on CPU during sending and receiving messages. When user
 * connects to the server, the connection itself consumes some CPU time.
 * At the end of the benchmark execution [stopUser] should be called.
 *
 * Because of the design of the coroutines tasks scheduler and channels, it is important to call [yield] sometimes to allow other
 * coroutines to work. This is necessary due to the fact that if a coroutine constantly has some work to do, like in this
 * case if a coroutine has an endless flow of messages, it will work without interruption, and other coroutines will have to
 * wait for this coroutine to end it's execution.
 * todo: remove the call of yield when this bug is fixed
 */
public class User(private val id: Long,
           public val activity: Double,
           private val messageChannel: Channel<Message?>,
           private val averageWork: Int) {
    public var sentMessages: Long = 0L
        private set
    public var receivedMessages: Long = 0L
        private set

    private val random = Random(id)
    private var messagesToSent: Double = activity

    private lateinit var friends: List<User>
    private lateinit var cumSumFriends : DoubleArray

    public lateinit var runCoroutine: Job

    public fun setFriends(friends : List<User>) {
        require(friends.isNotEmpty())
        this.friends = friends
        val cumSumFriends = DoubleArray(friends.size)
        cumSumFriends[0] = friends[0].activity
        for (i in 1 until friends.size) {
            cumSumFriends[i] = cumSumFriends[i - 1] + friends[i].activity
        }
        this.cumSumFriends = cumSumFriends
    }

    public fun startUser() {
        var yieldLoopCounter = 0L
        runCoroutine = CoroutineScope(context).launch {
            while (!stopped) {
                // if we can send a message, send it, otherwise wait on receive and receive a message
                if (messagesToSent >= 1) {
                    if (!sendMessage()) break
                } else {
                    val message = messageChannel.receive() ?: break
                    receiveAndProcessMessage(message)
                }
                // hint described in the class' comment section
                if (yieldLoopCounter++ % 61 == 5L) {
                    yield()
                }
            }
        }
    }

    private suspend fun sendMessage(): Boolean {
        val userChannelToSend = chooseUserToSend().messageChannel
        val now = System.nanoTime()
        val message = Message(id, now)
        if (userChannelToSend.offer(message)) {
            messagesToSent--
            sentMessages++
            doGeomDistrWork(averageWork)
            return true
        }
        when (userChannelToSend) {
            is BufferedChannel<Message?> -> {
                val messageChannel = this.messageChannel as BufferedChannel<Message?>
                return newSelect<Boolean> {
                    userChannelToSend.onSendNew(message) {
                        messagesToSent--
                        sentMessages++
                        doGeomDistrWork(averageWork)
                        true
                    }
                    messageChannel.onReceiveNew { message ->
                        if (message != null) {
                            receiveAndProcessMessage(message)
                            true
                        } else false
                    }
                }
            }
            is RendezvousChannelEuropar<Message?> -> {
                val messageChannel = this.messageChannel as RendezvousChannelEuropar<Message?>
                return selectEuropar<Boolean> {
                    userChannelToSend.onSendEuropar(message) {
                        messagesToSent--
                        sentMessages++
                        doGeomDistrWork(averageWork)
                        true
                    }
                    messageChannel.onReceiveEuropar { message ->
                        if (message != null) {
                            receiveAndProcessMessage(message)
                            true
                        } else false
                    }
                }
            }
            else -> {
                return select<Boolean> {
                    userChannelToSend.onSend(message) {
                        messagesToSent--
                        sentMessages++
                        doGeomDistrWork(averageWork)
                        true
                    }
                    messageChannel.onReceive { message ->
                        if (message != null) {
                            receiveAndProcessMessage(message)
                            true
                        } else false
                    }
                }
            }
        }
    }

    private fun receiveAndProcessMessage(message: Message) {
        messagesToSent += activity
        receivedMessages++
        doGeomDistrWork(averageWork)
    }

    public suspend fun stopUser() {
        messageChannel.send(null)
    }

    private fun chooseUserToSend(): User {
        var user : User = this
        while (this == user) {
            val randomDouble = random.nextDouble() * cumSumFriends.last()
            var insertionPoint = cumSumFriends.binarySearch(randomDouble)

            // binary search can return negative values. It indicates the position in the original collection where
            // the searched element can be inserted
            if (insertionPoint < 0) insertionPoint = -(insertionPoint + 1)

            // insertionPoint won't be out of bounds because randomDouble is less than or equals to the last number in the
            // cumSumFriends list
            user =  friends[insertionPoint]
        }
        return user
    }
}

/**
 * A message from one of the users to another one
 */
public class Message(private val userId: Long, public val nanos: Long)