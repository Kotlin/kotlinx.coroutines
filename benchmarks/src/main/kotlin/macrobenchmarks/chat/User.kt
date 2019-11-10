/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package macrobenchmarks.chat

import benchmarks.common.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
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
abstract class User(private val id: Long,
                    val activity: Double,
                    private val messageChannel: Channel<Message>,
                    private val averageWork: Int) {
    var sentMessages = 0L
        protected set

    var receivedMessages = 0L
        protected set

    protected val random = Random(id)

    private var messagesToSent: Double = activity

    lateinit var runCoroutine: Job

    fun startUser() {
        var yieldLoopCounter = 0L
        runCoroutine = CoroutineScope(context).launch {
            while (!stopped) {
                // receive messages while can
                while (true) {
                    val message = messageChannel.poll() ?: break
                    receiveAndProcessMessage(message)
                }
                // if we can send a message, send it, otherwise wait on receive and receive a message
                if (messagesToSent >= 1) {
                    sendMessage()
                } else {
                    val message = messageChannel.receiveOrClosed().valueOrNull ?: break
                    receiveAndProcessMessage(message)
                }
                // hint described in the class' comment section
                if (yieldLoopCounter++ % 61 == 5L) {
                    yield()
                }
            }
        }
    }

    private suspend fun sendMessage() {
        val userChannelToSend = chooseUserToSend().messageChannel
        val now = System.nanoTime()
        try {
            select<Unit> {
                userChannelToSend.onSend(Message(id, now)) {
                    messagesToSent--
                    sentMessages++
                    doGeomDistrWork(averageWork)
                }
                messageChannel.onReceiveOrClosed { message ->
                    if (!message.isClosed) {
                        receiveAndProcessMessage(message.value)
                    }
                }
            }
        } catch (ignored: ClosedSendChannelException) {
        } catch (ignored: IllegalStateException) {
        }
    }

    private fun receiveAndProcessMessage(message: Message) {
        messagesToSent += activity
        receivedMessages++
        doGeomDistrWork(averageWork)
    }

    fun stopUser() {
        messageChannel.close()
    }

    abstract fun chooseUserToSend(): User
}

/**
 * A message from one of the users to another one
 */
class Message(private val userId: Long, val nanos: Long)