package inmemorychat

import kotlinx.coroutines.channels.ClosedSendChannelException
import kotlinx.coroutines.runBlocking
import java.util.*
import kotlin.collections.ArrayList

/**
 * Generates commands [SendMessage] to the [UserWithSelect] and [UserWithOneJob] users.
 * Every user has multiple friends, and in order to choose a user that has more friends more often, every LoaderThread
 * computes cumulative sums of all users' friends, and when a thread wants to choose a user randomly, it generates a new random
 * number and finds it in the cumulative sums list using [List.binarySearch]. Thus a user that has more friends than other users
 * will be chosen more often.
 */
class Loader(users: List<User>, properties: BenchmarkProperties) {
    private val loaderThreads = ArrayList<Thread>()

    init {
        val threadNumToUsers = users.groupBy { (it.id % LOADER_THREADS_COUNT).toInt() }

        repeat(LOADER_THREADS_COUNT) {
            val threadUsers = threadNumToUsers[it]
            if (threadUsers != null) {
                val loaderThread = LoaderThread(it, threadUsers, properties)
                loaderThread.name = "LoaderThread-$it"
                loaderThread.isDaemon = true
                loaderThread.start()
                loaderThreads.add(loaderThread)
            }
        }
    }

    private class LoaderThread(val threadNum: Int, val users: List<User>, val properties: BenchmarkProperties) : Thread() {
        private val cumSumFriends = ArrayList<Int>(users.size)

        private val random = Random(42)

        init {
            cumSumFriends.add(0)
            for (i in 1 until users.size) {
                cumSumFriends.add(cumSumFriends[i - 1] + users[i].friends.size)
            }
        }

        override fun run() {
            while (!Thread.currentThread().isInterrupted) {
                try {
                    val nextInt = random.nextInt(cumSumFriends.last() - 1)
                    var insertionPoint = cumSumFriends.binarySearch(nextInt)

                    // binary search can return negative values. It indicates the position in the original collection where
                    // the searched element can be inserted
                    if (insertionPoint < 0) {
                        insertionPoint = -(insertionPoint + 1)
                    }
                    runBlocking {
                        // insertionPoint won't be out of bounds because nextInt is less than the last number in the cumSumFriends list
                        when (val user = users[insertionPoint]) {
                            is UserWithOneJob -> user.messagesChannel.send(SendMessage())
                            is UserWithSelect -> user.commandsChannel.send(SendMessage())
                            else -> {
//                                logger.warn("Unexpected type of user in a benchmark with properties $properties in thread $threadNum")
                            }
                        }
                    }
                }
                catch (ignored : InterruptedException) {
                    break
                }
                catch (ignored : ClosedSendChannelException) {
                    break
                }
                catch (e : Exception) {
//                    logger.error("Exception while running ${Thread.currentThread().name}", e)
                    throw e
                }
            }
        }
    }

    fun stop() {
        loaderThreads.forEach{ it.interrupt() }
    }
}