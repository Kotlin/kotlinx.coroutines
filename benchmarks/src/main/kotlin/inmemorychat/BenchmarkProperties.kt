package inmemorychat

import kotlinx.coroutines.channels.Channel
import kotlin.collections.ArrayList
import kotlin.collections.HashMap

// Benchmarks properties to monitor

/**
 * Underlying thread pool size for coroutines.
 */
val THREADS = listOf(4, 8, 16)
/**
 * Chat users count.
 */
val USER_COUNT = listOf(2000)
/**
 * Maximum percentage of all chat users a user can be friends with.
 */
val MAX_FRIENDS_PERCENTAGE = listOf(0.2)
/**
 * Coroutines channels type.
 */
val CHANNELS_TYPE = listOf(Channel.RENDEZVOUS, Channel.UNLIMITED, 1, 4, 16)
/**
 * The amount of time tokens that will be consumed on CPU. See [org.openjdk.jmh.infra.Blackhole.consumeCPU]
 */
val TOKENS = listOf<Long>(1000)
/**
 * Implementations of users that contain different ways to produce message flow and different ways to use coroutines channels.
 */
val USER_TYPE = listOf(UserType.USER_WITH_ONE_JOB, UserType.USER_WITH_TWO_JOBS, UserType.USER_WITH_SELECT)
/**
 * All the percentiles of latency the benchmark should count
 */
val PERCENTILE_TO_OUTPUT = listOf(50, 75, 90)
/**
 * The header for the output CSV file. It should be coordinated with [inmemorychat.BenchmarkProperties.toCSV] method.
 */
const val BENCHMARK_PROPERTIES_FIELDS = "threads,userCount,maxFriendsPercentage,channelType,tokens,userType,sentMessages,receivedMessages,50percentile,75percentile,90percentile"

// Benchmark properties that are not shown in the output file

/**
 * Execution time of each benchmark not including time to warm up.
 */
const val TIME_TO_LIVE_MS = 2000L
/**
 * Warm up time of each iteration.
 */
const val TIME_TO_WARM_UP_MS = 200L
/**
 * Warm up iterations count
 */
const val WARM_UP_COUNT = 5
/**
 * Number of threads that generate commands to users to send a message
 */
const val LOADER_THREADS_COUNT = 10
/**
 * CSV file containing the configurations and final metrics of the executed benchmarks
 */
const val BENCHMARK_OUTPUT_FILE = "results.csv"

/**
 * Class containing all the benchmark properties and metrics of the run benchmark
 */
class BenchmarkProperties(
        var threads: Int = 10,
        var userCount: Int = 1000,
        var maxFriendsPercentage: Double = 0.1,
        var channelType: Int = Channel.RENDEZVOUS,
        var tokens: Long = 2,
        var userType: UserType = UserType.USER_WITH_TWO_JOBS
) {
    var sentMessages = 0L

    var receivedMessages = 0L

    var latencies = HashMap<Int, Long>()

    override fun toString(): String {
        return "ChatConfiguration(threads=$threads, userCount=$userCount, maxFriendsPercentage=$maxFriendsPercentage, " +
                "channelType=$channelType, tokens=$tokens, userType=$userType, sentMessages=$sentMessages, receivedMessages=$receivedMessages)"
    }

    fun toCSV(): String {
        val latenciesString = StringBuilder()
        for (percentile in PERCENTILE_TO_OUTPUT) {
            latenciesString.append(",").append(latencies[percentile])
        }
        val channelTypeString = when(channelType) {
            Channel.RENDEZVOUS -> "RendezvousChannel"
            Channel.UNLIMITED -> "LinkedListChannel"
            Channel.CONFLATED -> "ConflatedChannel"
            Channel.BUFFERED -> "BufferedChannel"
            else -> "ArrayChannel($channelType)"
        }
        return "$threads,$userCount,$maxFriendsPercentage,$channelTypeString,$tokens,$userType,$sentMessages,$receivedMessages$latenciesString"
    }

    fun toArray() : Array<String> {
        return arrayOf(threads.toString(), userCount.toString(), maxFriendsPercentage.toString(), channelType.toString(), tokens.toString(), userType.toString())
    }

    companion object {
        fun parseArray(array : Array<String>) : BenchmarkProperties {
            return BenchmarkProperties(array[0].toInt(), array[1].toInt(), array[2].toDouble(), array[3].toInt(), array[4].toLong(), UserType.valueOf(array[5]))
        }
    }
}

enum class UserType {
    USER_WITH_ONE_JOB,
    USER_WITH_TWO_JOBS,
    USER_WITH_SELECT
}

fun createBenchmarkPropertiesList() : List<BenchmarkProperties> {
    val list = ArrayList<BenchmarkProperties>()
    for (threads in THREADS) {
        for (userCount in USER_COUNT) {
            for (maxFriendsPercentage in MAX_FRIENDS_PERCENTAGE) {
                for (channelType in CHANNELS_TYPE) {
                    for (tokens in TOKENS) {
                        for (userType in USER_TYPE) {
                            list.add(
                                    BenchmarkProperties(
                                            threads,
                                            userCount,
                                            maxFriendsPercentage,
                                            channelType,
                                            tokens,
                                            userType
                                    )
                            )
                        }
                    }
                }
            }
        }
    }
    return list
}