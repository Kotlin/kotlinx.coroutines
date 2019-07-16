package inmemorychat

import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.channels.ClosedSendChannelException
import java.util.*
import java.util.concurrent.ThreadLocalRandom
import kotlin.collections.ArrayList

/**
 * An abstract class for server-side chat users.
 * Every user has its own channel through which users can get messages from other users [receiveAndProcessMessage],
 * users can send messages to their friends' channels as well [sendMessage].
 * User contains sent and received messages metrics.
 * To emulate real world chat servers, some work will be executed on CPU during sending and receiving messages. When user
 * connects to the server, the connection itself consumes some CPU time.
 * At the end of the benchmark execution [stopUser] should be called.
 */
open class User(val id: Long, val messagesChannel: Channel<Message>, val properties: BenchmarkProperties,
                @Volatile var shouldCountMetrics: Boolean) {
    var sentMessages = 0L
        protected set

    var receivedMessages = 0L
        protected set

    val friends = ArrayList<Channel<Message>>()

    protected val random = Random(42)

    private fun doSomeWorkOnCpu() {
        // We use geometric distribution here
        val p = 1.0 / properties.tokens
        val r = ThreadLocalRandom.current()
        while (true) {
            if (r.nextDouble() < p) break
        }
    }

    fun addFriend(userChannel : Channel<Message>) {
        friends.add(userChannel)
    }

    protected suspend fun sendMessage() {
        doSomeWorkOnCpu()
        if (friends.isEmpty()) {
            return
        }
        val friendNum = random.nextInt(friends.size)
        val now = System.nanoTime()
        try {
            friends[friendNum].send(UserMessage(id, now))
            if (shouldCountMetrics) {
                sentMessages++
            }
        } catch (ignored : ClosedSendChannelException) {}
        doSomeWorkOnCpu()
    }

    protected fun receiveAndProcessMessage(message : Message) {
        if (message !is UserMessage) {
            return
        }
        doSomeWorkOnCpu()
        if (shouldCountMetrics) {
            receivedMessages++
        }
        doSomeWorkOnCpu()
    }

    open fun stopUser() {}
}

open class Message

/**
 * A command that means that a user should send a message to one of user's friends
 */
class SendMessage : Message()

/**
 * A message from one of the users to another one
 */
class UserMessage(private val userId : Long, val nanos : Long) : Message()