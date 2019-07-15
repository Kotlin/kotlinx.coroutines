@file:JvmName("InMemoryChatBenchmark")

package inmemorychat

import kotlinx.coroutines.asCoroutineDispatcher
import java.io.File
import java.util.*
import java.util.concurrent.Executors
import kotlin.collections.ArrayList
import kotlin.math.floor

@Volatile
var context = Executors.newFixedThreadPool(10) {
    val newThread = Executors.defaultThreadFactory().newThread(it)
    newThread.isDaemon = true
    newThread
}.asCoroutineDispatcher()

val propertiesList = createBenchmarkPropertiesList()

//val logger = org.slf4j.LoggerFactory.getLogger("InMemoryChatBenchmark")

fun main() {
//    logger.debug("Benchmarks count ${propertiesList.size}")

    for (properties in propertiesList) {
        context = Executors.newFixedThreadPool(properties.threads) {
            val newThread = Executors.defaultThreadFactory().newThread(it)
            newThread.isDaemon = true
            newThread
        }.asCoroutineDispatcher()

        warmUp(properties)

        val users = ArrayList<User>()
        val random = Random(42)
        val server = Server(properties)
        var loader : Loader? = null
        try {
            createUsers(users, server, random, true, properties)
            loader = initLoaderIfNeeded(users, properties)

            Thread.sleep(TIME_TO_LIVE_MS)

            collectBenchmarkMetrics(users, properties)
        }
        finally {
            loader?.stop()
            stopUsers(users)
            context.close()
            users.clear()
        }
    }

    File(BENCHMARK_OUTPUT_FILE).printWriter().use { out ->
        out.println(BENCHMARK_PROPERTIES_FIELDS)
        propertiesList.forEach {
            out.println(it.toCSV())
        }
    }
}

private fun warmUp(properties: BenchmarkProperties) {
    val users = ArrayList<User>()
    val random = Random(42)
    repeat(WARM_UP_COUNT) {
        val server = Server(properties)
        var loader : Loader? = null
        try {
            createUsers(users, server, random, false, properties)
            loader = initLoaderIfNeeded(users, properties)
            Thread.sleep(TIME_TO_WARM_UP_MS)
//            logger.trace("${it + 1} warm up, ${System.currentTimeMillis()}")
        }
        finally {
            stopUsers(users)
            users.clear()
            loader?.stop()
        }
    }
}

private fun createUsers(users: ArrayList<User>, server: Server, random: Random, shouldCountMetrics : Boolean,
                        properties : BenchmarkProperties) {
    repeat(properties.userCount) {
        val user = server.registerClient(shouldCountMetrics)
        users.add(user)
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
        friends.forEach(user::addFriend)
    }
}

private fun initLoaderIfNeeded(users: List<User>, properties : BenchmarkProperties) : Loader? {
    if (properties.userType != UserType.USER_WITH_TWO_JOBS) {
        return Loader(users, properties)
    }
    return null
}

private fun collectBenchmarkMetrics(users: ArrayList<User>, properties: BenchmarkProperties) {
    val sortedLatencies = TreeMap<Long, Int>()
    for (user in users) {
        user.shouldCountMetrics = false
        properties.sentMessages += user.sentMessages
        properties.receivedMessages += user.receivedMessages
        for (entry in user.getLatencies()) {
            sortedLatencies.compute(entry.key) { _, v ->
                if (v == null) {
                    entry.value
                }
                else {
                    v + entry.value
                }
            }
        }
    }
    // Computing required percentiles
    val entriesList = ArrayList<Map.Entry<Long, Int>>(sortedLatencies.entries)
    val latenciesList = ArrayList<Int>()
    latenciesList.add(0)
    // Compute cumulative sums of numbers of registered latencies. Thus the last element of list contains the number of
    // all registered latencies.
    for (entry in sortedLatencies.entries) {
        latenciesList.add(latenciesList.last() + entry.value)
    }
    // Find required percentiles. If every latency occurred in the latenciesList the number of times this latency
    // was registered, we could easily find the required latency by finding an element of nth position. But the latenciesList
    // would contain a lot of elements in this case, so the idea here is to find the closest element to the
    // (number of registered latencies * required percentile) in the list of cumulative sums.
    for (percentile in PERCENTILE_TO_OUTPUT) {
        var insertionPoint = latenciesList.binarySearch(floor(latenciesList.last() * percentile / 100.0).toInt())
        if (insertionPoint < 0) {
            insertionPoint = -(insertionPoint + 1)
        }
        val latency = entriesList[insertionPoint].key
        properties.latencies[percentile] = latency
    }
}

private fun stopUsers(users: ArrayList<User>) {
    users.forEach(User::stopUser)
}