package inmemorychat

import kotlinx.coroutines.channels.Channel
import org.openjdk.jmh.infra.Blackhole
import java.time.Instant
import java.util.*
import java.util.concurrent.ConcurrentHashMap
import kotlin.collections.ArrayList

/**
 * An abstract class for server-side chat users.
 * Every user has its own channel through which users can get messages from other users [receiveAndProcessMessage],
 * users can send messages to their friends' channels as well [sendMessage].
 * User contains sent and received messages metrics, messages latencies. Message latency is a delay between the time
 * the message was sent and the time the message was received.
 * To emulate real world chat servers, some work will be executed on CPU during sending and receiving messages. When user
 * connects to the server, the connection itself consumes some CPU time.
 * At the end of the benchmark execution [stopUser] should be called.
 */
open class User(private val server: Server, val id: Long, val messagesChannel: Channel<Message>, val properties: BenchmarkProperties,
                @Volatile var shouldCountMetrics: Boolean) {
    var sentMessages = 0L
        protected set

    var receivedMessages = 0L
        protected set

    val friends = ArrayList<Long>()

    protected val random = Random(42)

    /**
     * Latency to the number of times this latency occurred
     */
    private val latencies = ConcurrentHashMap<Long, Int>()

    private fun doSomeWorkOnCpu() {
        Blackhole.consumeCPU(properties.tokens)
    }

    fun addFriend(userId: Long) {
        friends.add(userId)
    }

    protected suspend fun sendMessage() {
        doSomeWorkOnCpu()
        if (friends.isEmpty()) {
            return
        }
        val friendNum = random.nextInt(friends.size)
        val now = Instant.now()
        server.sendMessage(friends[friendNum], UserMessage(id, now.epochSecond, now.nano))
        if (shouldCountMetrics) {
            sentMessages++
        }
        doSomeWorkOnCpu()
    }

    protected fun receiveAndProcessMessage(message : Message) {
        if (message !is UserMessage) {
            return
        }
        doSomeWorkOnCpu()
        if (shouldCountMetrics) {
            val receivingInstant = Instant.now()
            val currentLatencyNs = (receivingInstant.epochSecond - message.seconds) * 1_000_000_000 + (receivingInstant.nano - message.nanos)
            latencies.compute(currentLatencyNs) { _, v ->
                if (v == null) {
                    1
                }
                else {
                    v + 1
                }
            }
            receivedMessages++
        }
        doSomeWorkOnCpu()
    }

    open fun stopUser() {}

    fun getLatencies() : HashMap<Long, Int> {
        return HashMap(latencies)
    }
}