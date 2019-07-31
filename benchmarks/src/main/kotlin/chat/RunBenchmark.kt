@file:JvmName("RunBenchmark")

package chat

import kotlinx.coroutines.channels.Channel
import org.apache.commons.math3.distribution.PoissonDistribution
import java.io.Closeable
import java.io.File
import java.util.*
import kotlin.collections.ArrayList

const val fileName = "chat_"

fun main(args: Array<String>) {
    val benchmarkIteration = args[0].toInt() + 1
    val propsArray = args.drop(1).toTypedArray()
    val properties = BenchmarkConfiguration.parseArray(propsArray)

    val dispatcher = properties.dispatcherType.create(properties.threads)

    // warming up
    println("Start warming up")
    val mean = 100.0

    repeat(WARM_UP_ITERATIONS) {
        runBenchmarkIteration(it + 1, mean, properties, true)
    }
    println("Warming up results were:")
    repeat(BENCHMARK_ITERATIONS) {
        println("${it + 1} run sentMessages ${properties.sentMessagesPerRun[it]}, receivedMessages ${properties.receivedMessagesPerRun[it]}")
    }
    properties.sentMessagesPerRun.clear()
    properties.receivedMessagesPerRun.clear()

    // running benchmark
    println("Start running benchmark")
    repeat(BENCHMARK_ITERATIONS) {
        runBenchmarkIteration(it + 1, mean, properties, true)
    }

    // closing coroutineDispatcher
    if (dispatcher is Closeable) {
        dispatcher.close()
    }

    File("$BENCHMARK_OUTPUT_FOLDER/$fileName$benchmarkIteration").printWriter().use { out ->
        out.println(properties.toCSV())
    }

    println("Benchmark results were:")
    repeat(BENCHMARK_ITERATIONS) {
        println("${it + 1} run sentMessages ${properties.sentMessagesPerRun[it]}, receivedMessages ${properties.receivedMessagesPerRun[it]}")
    }
}

private fun runBenchmarkIteration(iteration : Int,
                                  mean: Double,
                                  configuration: BenchmarkConfiguration,
                                  shouldCountMetrics: Boolean) {
    println("$iteration iteration")
    val poissonDistribution = PoissonDistribution(mean)
    poissonDistribution.reseedRandomGenerator(42)
    val users = ArrayList<User>()
    val server = Server(configuration)
    try {
        createUsers(users, server, mean, poissonDistribution, Random(42), configuration)

        Thread.sleep(BENCHMARK_TIME_MS)

        if (shouldCountMetrics) {
            collectBenchmarkMetrics(users, configuration)
        }
    } finally {
        stopUsers(users)
    }
}

private fun createUsers(users: ArrayList<User>,
                        server: Server,
                        mean : Double,
                        poissonDistribution: PoissonDistribution,
                        random: Random,
                        configuration: BenchmarkConfiguration) {
    val first = System.currentTimeMillis()
    var sumPoissonDistribution = 0L
    repeat(configuration.userCount) {
        val ctm1 = System.currentTimeMillis()
        val sample = poissonDistribution.sample()
        val ctm2 = System.currentTimeMillis()
        sumPoissonDistribution += ctm2 - ctm1
        val sendingMessageSpeed = sample / mean
        val user = server.registerClient(true, sendingMessageSpeed)
        users.add(user)
    }
    val second = System.currentTimeMillis()

    when (configuration.benchmarkMode) {
        BenchmarkModes.USER_WITH_FRIENDS -> {
            addFriendsToUsers(configuration, users.map { user -> user as UserWithFriends }.toList(), random)
        }
        BenchmarkModes.USER_WITHOUT_FRIENDS -> {
            val cumSumFriends = ArrayList<Double>(users.size)
            for (i in 0 until users.size) {
                if (cumSumFriends.isEmpty()) {
                    cumSumFriends.add(users[i].sendingMessageSpeed)
                }
                else {
                    cumSumFriends.add(cumSumFriends[i - 1] + users[i].sendingMessageSpeed)
                }
            }
            for (user in users) {
                user as UserWithoutFriends
                user.setUsers(users, cumSumFriends)
            }
        }
    }

    val third = System.currentTimeMillis()

    for (user in users) {
        user.startUserScenario()
    }

    val fourth = System.currentTimeMillis()

    println("Creating users : ${second - first}, adding contacts : ${third - second}, starting scenarios : ${fourth - third}, using poisson distribution time $sumPoissonDistribution")
}

private fun addFriendsToUsers(configuration: BenchmarkConfiguration, users: List<UserWithFriends>, random: Random) {
    val friendsCount = (configuration.userCount * configuration.maxFriendsPercentage).toInt()

    for ((userIndex, user) in users.withIndex()) {
        val randomAmountOfFriends = random.nextInt(friendsCount) + 1
        val friends = HashSet<Int>(randomAmountOfFriends * 2 + 1)
        friends.add(userIndex)
        repeat(randomAmountOfFriends) {
            var userNum = random.nextInt(users.size)
            while (!friends.add(userNum)) {
                userNum = random.nextInt(users.size)
            }
        }
        friends.remove(userIndex)
        val friendsChannels = ArrayList<Channel<Message>>(randomAmountOfFriends)
        for (userNum in friends) {
            friendsChannels.add(users[userNum].messagesChannel)
        }
        user.setFriends(friendsChannels)
    }
}

private fun collectBenchmarkMetrics(users: ArrayList<User>, configuration: BenchmarkConfiguration) {
    for (user in users) {
        user.shouldCountMetrics = false
    }
    var sentMessages = 0L
    var receivedMessages = 0L
    for (user in users) {
        sentMessages += user.sentMessages
        receivedMessages += user.receivedMessages
    }
    configuration.sentMessagesPerRun.add(sentMessages)
    configuration.receivedMessagesPerRun.add(receivedMessages)
}

private fun stopUsers(users: ArrayList<User>) {
    users.forEach(User::stopUser)
}