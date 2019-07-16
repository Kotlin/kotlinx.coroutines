@file:JvmName("RunBenchmark")

package inmemorychat

import java.io.Closeable
import java.io.File
import java.util.*

const val fileName = "inmemorychat_"

fun main(args: Array<String>) {
    val benchmarkIteration = args[0]
    val propsArray = args.drop(1).toTypedArray()
    val properties = BenchmarkProperties.parseArray(propsArray)

    val context = properties.dispatcherType.create(properties.threads)

    // warming up
    var random = Random(42)
    repeat(WARM_UP_ITERATIONS) {
        runBenchmarkIteration(it + 1, random, properties, false)
    }

    // running benchmark
    random = Random(42)
    repeat(BENCHMARK_ITERATIONS) {
        runBenchmarkIteration(it + 1, random, properties, true)
    }

    // closing coroutineDispatcher
    if (context is Closeable) {
        context.close()
    }

    File("$BENCHMARK_OUTPUT_FOLDER/$fileName$benchmarkIteration").printWriter().use { out ->
        out.println(properties.toCSV())
    }
}

private fun runBenchmarkIteration(iteration : Int, random: Random, properties: BenchmarkProperties, shouldCountMetrics: Boolean) {
    val users = ArrayList<User>()
    val server = Server(properties)
    var loader: Loader? = null
    try {
        createUsers(users, server, random, shouldCountMetrics, properties)
        loader = initLoaderIfNeeded(users, properties)

        Thread.sleep(BENCHMARK_TIME_MS)

        if (shouldCountMetrics) {
            collectBenchmarkMetrics(users, properties)
        }

//        logger.trace("$iteration iteration")
        println("$iteration iteration")
    } finally {
        stopUsers(users)
        loader?.stop()
    }
}

private fun createUsers(users: ArrayList<User>, server: Server, random: Random, shouldCountMetrics: Boolean,
                        properties: BenchmarkProperties) {
    val hashMap = HashMap<Long, User>()
    repeat(properties.userCount) {
        val user = server.registerClient(shouldCountMetrics)
        users.add(user)
        hashMap[user.id] = user
    }

    val friendsCount = (properties.userCount * properties.maxFriendsPercentage).toInt()
    for (user in users) {
        val friends = HashSet<Long>()
        friends.add(user.id)

        repeat(random.nextInt(friendsCount)) {
            var userNum = random.nextInt(users.size)
            while (friends.contains(users[userNum].id)) {
                userNum = random.nextInt(users.size)
            }
            friends.add(users[userNum].id)
        }

        friends.remove(user.id)
        friends.forEach { user.addFriend(hashMap[it]!!.messagesChannel) }
    }
}

private fun initLoaderIfNeeded(users: List<User>, properties: BenchmarkProperties): Loader? {
    if (properties.benchmarkMode != BenchmarkModes.USER_WITH_TWO_JOBS) {
        return Loader(users, properties)
    }
    return null
}

private fun collectBenchmarkMetrics(users: ArrayList<User>, properties: BenchmarkProperties) {
    for (user in users) {
        user.shouldCountMetrics = false
    }
    var sentMessages = 0L
    var receivedMessages = 0L
    for (user in users) {
        sentMessages += user.sentMessages
        receivedMessages += user.receivedMessages
    }
    properties.sentMessagesPerRun.add(sentMessages)
    properties.receivedMessagesPerRun.add(receivedMessages)
}

private fun stopUsers(users: ArrayList<User>) {
    users.forEach(User::stopUser)
}