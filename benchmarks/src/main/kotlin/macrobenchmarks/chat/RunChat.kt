/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmName("RunChat")

package macrobenchmarks.chat

import kotlinx.coroutines.*
import org.apache.commons.math3.distribution.*
import java.io.*
import java.util.*
import java.util.concurrent.atomic.*
import kotlin.collections.ArrayList

var context = DispatcherTypes.Experimental.create(1)
private const val SHOULD_PRINT_DEBUG_OUTPUT = true

@Volatile
var stopped = false

@Suppress("ConstantConditionIf")
fun main(args: Array<String>) {
    val configuration = BenchmarkConfiguration.parseBenchmarkArgs(args)

    // warming up
    println("Start warming up")
    val mean = 100.0

    var benchmarkResults = BenchmarkResults()
    repeat(WARM_UP_ITERATIONS) {
        runBenchmarkIteration(it + 1, mean, configuration, benchmarkResults)
    }

    if (SHOULD_PRINT_DEBUG_OUTPUT) {
        println("Warming up results were:")
        repeat(WARM_UP_ITERATIONS) {
            println("${it + 1} run sentMessages ${benchmarkResults.sentMessagesPerRun[it]}, receivedMessages ${benchmarkResults.receivedMessagesPerRun[it]}")
        }
    }

    benchmarkResults = BenchmarkResults()
    // running benchmark
    println("Start running benchmark")
    repeat(ITERATIONS) {
        runBenchmarkIteration(it + 1, mean, configuration, benchmarkResults)
    }

    FileOutputStream(BENCHMARK_OUTPUT_FILE, true).bufferedWriter().use { writer ->
        writer.append("${configuration.toCSV()},${benchmarkResults.toCSV()}\n")
    }

    if (SHOULD_PRINT_DEBUG_OUTPUT) {
        println("Benchmark results were:")
        repeat(ITERATIONS) {
            println("${it + 1} run sentMessages ${benchmarkResults.sentMessagesPerRun[it]}, receivedMessages ${benchmarkResults.receivedMessagesPerRun[it]}")
        }
    }
}

@Suppress("ConstantConditionIf")
private fun runBenchmarkIteration(iteration: Int,
                                  mean: Double,
                                  configuration: BenchmarkConfiguration,
                                  benchmarkResults : BenchmarkResults) {
    stopped = false
    context = configuration.dispatcherType.create(configuration.threads)

    if (SHOULD_PRINT_DEBUG_OUTPUT) {
        println("$iteration iteration")
    }

    val poissonDistribution = PoissonDistribution(mean)
    poissonDistribution.reseedRandomGenerator(42)
    val users = ArrayList<User>()

    createUsers(users, mean, poissonDistribution, Random(42), configuration)

    Thread.sleep(BENCHMARK_TIME_MS)

    stopUsers(users)
    waitForCoroutines(users)
    collectBenchmarkMetrics(users, benchmarkResults)

    val context = context
    // closing coroutineDispatcher
    if (context is Closeable) {
        context.close()
    }
}

@Suppress("ConstantConditionIf")
private fun createUsers(users: ArrayList<User>,
                        mean: Double,
                        poissonDistribution: PoissonDistribution,
                        random: Random,
                        configuration: BenchmarkConfiguration) {
    require(configuration.users > 3) { "User number should be more than 3" }
    val idSequence = AtomicLong()
    val startCreatingUsers = System.currentTimeMillis()
    repeat(configuration.users) {
        val sample = poissonDistribution.sample()
        val activity = sample / mean
        val userId = idSequence.incrementAndGet()
        val messageChannel = configuration.channelCreator.create<Message>()
        val user = User(userId, activity, messageChannel, configuration.averageWork)
        users.add(user)
    }
    val endCreatingUsers = System.currentTimeMillis()
    addFriendsToUsers(configuration, users, random)
    val endAddingContacts = System.currentTimeMillis()

    users.forEach(User::startUser)

    if (SHOULD_PRINT_DEBUG_OUTPUT) {
        println("Creating users : ${endCreatingUsers - startCreatingUsers}, adding contacts : ${endAddingContacts - endCreatingUsers}")
    }
}

private fun addFriendsToUsers(configuration: BenchmarkConfiguration, users: List<User>, random: Random) {
    val friendsCount = (configuration.users * configuration.maxFriendsPercentage).toInt()

    for (user in users) {
        val randomAmountOfFriends = random.nextInt(friendsCount) + 1
        // if the number of friends is too big, use not that fast but stable method. If we manually
        // add friends it will be painfully slow
        if (randomAmountOfFriends > 0.6 * users.size) {
            user.setFriends(users.shuffled(random).take(randomAmountOfFriends))
            continue
        }

        val friendsNums = HashSet<Int>(randomAmountOfFriends * 2 + 1)
        repeat(randomAmountOfFriends) {
            var userNum = random.nextInt(users.size)
            while (!friendsNums.add(userNum)) {
                userNum = random.nextInt(users.size)
            }
        }
        val friends = ArrayList<User>(randomAmountOfFriends)
        for (userNum in friendsNums) {
            friends.add(users[userNum])
        }
        user.setFriends(friends)
    }
}

private fun stopUsers(users: ArrayList<User>) {
    stopped = true
    users.forEach(User::stopUser)
}

private fun waitForCoroutines(users : ArrayList<User>) {
    runBlocking {
        for (user in users) {
            user.runCoroutine.join()
        }
    }
}

private fun collectBenchmarkMetrics(users: ArrayList<User>, results: BenchmarkResults) {
    var sentMessages = 0L
    var receivedMessages = 0L
    for (user in users) {
        sentMessages += user.sentMessages
        receivedMessages += user.receivedMessages
    }
    results.sentMessagesPerRun.add(sentMessages.toDouble() / BENCHMARK_TIME_MS)
    results.receivedMessagesPerRun.add(receivedMessages.toDouble() / BENCHMARK_TIME_MS)
}