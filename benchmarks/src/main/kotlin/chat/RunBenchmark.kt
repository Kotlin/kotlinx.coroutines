@file:JvmName("RunBenchmark")
@file:Suppress("ConstantConditionIf")

package chat

import kotlinx.coroutines.channels.Channel
import org.apache.commons.math3.distribution.PoissonDistribution
import java.io.Closeable
import java.io.FileOutputStream
import java.util.*
import java.util.concurrent.atomic.AtomicLong
import kotlin.collections.ArrayList

var context = DispatcherTypes.FORK_JOIN.create(1)
const val shouldPrintDebugOutput = false

fun main(args: Array<String>) {
    val propsArray = args.drop(1).toTypedArray()
    val properties = BenchmarkConfiguration.parseArray(propsArray)

    context = properties.dispatcherType.create(properties.threads)

    // warming up
    println("Start warming up")
    val mean = 100.0

    repeat(WARM_UP_ITERATIONS) {
        runBenchmarkIteration(it + 1, mean, properties, true)
    }

    if (shouldPrintDebugOutput) {
        println("Warming up results were:")
        repeat(BENCHMARK_ITERATIONS) {
            println("${it + 1} run sentMessages ${properties.sentMessagesPerRun[it]}, receivedMessages ${properties.receivedMessagesPerRun[it]}")
        }
    }

    properties.sentMessagesPerRun.clear()
    properties.receivedMessagesPerRun.clear()

    // running benchmark
    println("Start running benchmark")
    repeat(BENCHMARK_ITERATIONS) {
        runBenchmarkIteration(it + 1, mean, properties, true)
    }

    val context = context
    // closing coroutineDispatcher
    if (context is Closeable) {
        context.close()
    }

    FileOutputStream("$BENCHMARK_OUTPUT_FOLDER/$BENCHMARK_OUTPUT_FILE", true).bufferedWriter().use { writer ->
        writer.append(properties.toCSV())
        writer.newLine()
    }

    if (shouldPrintDebugOutput) {
        println("Benchmark results were:")
        repeat(BENCHMARK_ITERATIONS) {
            println("${it + 1} run sentMessages ${properties.sentMessagesPerRun[it]}, receivedMessages ${properties.receivedMessagesPerRun[it]}")
        }
    }
}

private fun runBenchmarkIteration(iteration: Int,
                                  mean: Double,
                                  configuration: BenchmarkConfiguration,
                                  shouldCountMetrics: Boolean) {
    if (shouldPrintDebugOutput) {
        println("$iteration iteration")
    }

    val poissonDistribution = PoissonDistribution(mean)
    poissonDistribution.reseedRandomGenerator(42)
    val users = ArrayList<User>()
    var usersStopped = false
    try {
        createUsers(users, mean, poissonDistribution, Random(42), configuration)

        Thread.sleep(BENCHMARK_TIME_MS)

        stopUsers(users)
        usersStopped = true
        if (shouldCountMetrics) {
            collectBenchmarkMetrics(users, configuration)
        }
    } finally {
        if (!usersStopped) {
            stopUsers(users)
        }
    }
}

private fun createUsers(users: ArrayList<User>,
                        mean: Double,
                        poissonDistribution: PoissonDistribution,
                        random: Random,
                        configuration: BenchmarkConfiguration) {
    val first = System.currentTimeMillis()
    var sumPoissonDistribution = 0L
    val idSequence = AtomicLong()
    repeat(configuration.users) {
        val ctm1 = System.currentTimeMillis()
        val sample = poissonDistribution.sample()
        val ctm2 = System.currentTimeMillis()
        sumPoissonDistribution += ctm2 - ctm1
        val activity = sample / mean
        val user = registerClient(idSequence, configuration, activity)
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
                    cumSumFriends.add(users[i].activity)
                } else {
                    cumSumFriends.add(cumSumFriends[i - 1] + users[i].activity)
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
        user.startUser()
    }

    val fourth = System.currentTimeMillis()

    if (shouldPrintDebugOutput) {
        println("Creating users : ${second - first}, adding contacts : ${third - second}, starting scenarios : ${fourth - third}, using poisson distribution time $sumPoissonDistribution")
    }
}

fun registerClient(idSequence : AtomicLong, configuration: BenchmarkConfiguration, activity : Double): User {
    val userId = idSequence.incrementAndGet()
    val messageChannel = configuration.channelType.createChannel<Message>()

    return when (configuration.benchmarkMode) {
        BenchmarkModes.USER_WITH_FRIENDS -> UserWithFriends(userId, activity, messageChannel, configuration)
        BenchmarkModes.USER_WITHOUT_FRIENDS -> UserWithoutFriends(userId, activity, messageChannel, configuration)
    }
}

private fun addFriendsToUsers(configuration: BenchmarkConfiguration, users: List<UserWithFriends>, random: Random) {
    val friendsCount = (configuration.users * configuration.maxFriendsPercentage).toInt()

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
            friendsChannels.add(users[userNum].messageChannel)
        }
        user.setFriends(friendsChannels)
    }
}

private fun collectBenchmarkMetrics(users: ArrayList<User>, configuration: BenchmarkConfiguration) {
    var sentMessages = 0L
    var receivedMessages = 0L
    for (user in users) {
        sentMessages += user.sentMessages
        receivedMessages += user.receivedMessages
    }
    configuration.sentMessagesPerRun.add(sentMessages.toDouble() / BENCHMARK_TIME_MS)
    configuration.receivedMessagesPerRun.add(receivedMessages.toDouble() / BENCHMARK_TIME_MS)
}

private fun stopUsers(users: ArrayList<User>) {
    users.forEach(User::stopUser)
}