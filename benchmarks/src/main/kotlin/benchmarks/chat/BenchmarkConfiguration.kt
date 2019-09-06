package benchmarks.chat

import kotlinx.coroutines.CoroutineDispatcher
import kotlinx.coroutines.asCoroutineDispatcher
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.scheduling.ExperimentalCoroutineDispatcher
import org.nield.kotlinstatistics.standardDeviation
import java.util.concurrent.ForkJoinPool

/**
 * Execution time of each benchmark.
 */
const val BENCHMARK_TIME_MS = 2000L
/**
 * Warm up iterations count
 */
const val WARM_UP_ITERATIONS = 3
/**
 * Benchmark iterations count
 */
const val ITERATIONS = 5
/**
 * CSV file containing the configurations and final metrics of the executed benchmarks
 */
const val BENCHMARK_OUTPUT_FILE = "results.csv"
/**
 * Folder containing all benchmark output files
 */
const val BENCHMARK_OUTPUT_FOLDER = "out/"

// Configurations we want to test in the benchmark

/**
 * Underlying thread pool size for coroutines.
 */
private val THREADS = listOf(1, 4, 8, 16)
/**
 * Chat users count.
 */
private val USER_COUNT = listOf(10000)
/**
 * Maximum percentage of all chat users a user can be friends with.
 */
private val MAX_FRIENDS_PERCENTAGE = listOf(0.2)
/**
 * The average amount work that will be executed on CPU.
 */
private val AVERAGE_WORK = listOf(40, 80)

enum class BenchmarkModes {
    CHOOSE_RANDOM_FRIEND, // benchmark mode that sets to users some friends and lets users to send a message to a random friend
    CHOOSE_BASED_ON_ACTIVITY // benchmark mode that lets a user to choose another user to write based on users' activity
}

enum class ChannelCreator(private val capacity: Int) {
    RENDEZVOUS(Channel.RENDEZVOUS),
    BUFFERED_1(1),
    BUFFERED_2(2),
    BUFFERED_4(4),
    BUFFERED_32(32),
    BUFFERED_128(128),
    BUFFERED_UNLIMITED(Channel.UNLIMITED);

    fun <T> create(): Channel<T> = Channel(capacity)
}

enum class DispatcherTypes(val create: (parallelism: Int) -> CoroutineDispatcher) {
    FORK_JOIN({ parallelism -> ForkJoinPool(parallelism).asCoroutineDispatcher() }),
    EXPERIMENTAL({ parallelism -> ExperimentalCoroutineDispatcher(corePoolSize = parallelism, maxPoolSize = parallelism) })
}

val allConfigurations: List<BenchmarkConfiguration>
    get() {
        val list = ArrayList<BenchmarkConfiguration>()
        for (threads in THREADS) {
            for (userCount in USER_COUNT) {
                for (maxFriendsPercentage in MAX_FRIENDS_PERCENTAGE) {
                    for (channelCreator in ChannelCreator.values()) {
                        for (tokens in AVERAGE_WORK) {
                            for (userType in BenchmarkModes.values()) {
                                for (dispatcherType in DispatcherTypes.values()) {
                                    list.add(
                                            BenchmarkConfiguration(
                                                    threads,
                                                    userCount,
                                                    maxFriendsPercentage,
                                                    channelCreator,
                                                    tokens,
                                                    userType,
                                                    dispatcherType
                                            )
                                    )
                                }
                            }
                        }
                    }
                }
            }
        }
        return list
    }

/**
 * Class containing all the benchmark configuration and metrics of the run benchmark
 */
class BenchmarkConfiguration(
        var threads: Int,
        var users: Int,
        var maxFriendsPercentage: Double,
        var channelCreator: ChannelCreator,
        var averageWork: Int,
        var benchmarkMode: BenchmarkModes,
        var dispatcherType: DispatcherTypes
) {
    fun configurationToString() : String {
        return "[threads=$threads, users=$users, maxFriendsPercentage=$maxFriendsPercentage, channelCreator=$channelCreator, averageWork=$averageWork, benchmarkMode=$benchmarkMode, dispatcherType=$dispatcherType]"
    }

    fun toCSV(): String {
        return "$threads,$users,$maxFriendsPercentage,$channelCreator,$averageWork,$benchmarkMode,$dispatcherType"
    }

    fun configurationToArgsArray() : Array<String> {
        return arrayOf(threads.toString(), users.toString(), maxFriendsPercentage.toString(), channelCreator.toString(), averageWork.toString(), benchmarkMode.toString(), dispatcherType.toString())
    }

    companion object {
        fun parseBenchmarkArgs(array : Array<String>) : BenchmarkConfiguration {
            val threads = array[0].toInt()
            val userCount = array[1].toInt()
            val maxFriendsPercentage = array[2].toDouble()
            val channelCreator = ChannelCreator.valueOf(array[3])
            val averageWork = array[4].toInt()
            val benchmarkMode = BenchmarkModes.valueOf(array[5])
            val dispatcherType = DispatcherTypes.valueOf(array[6])
            return BenchmarkConfiguration(threads, userCount, maxFriendsPercentage, channelCreator, averageWork, benchmarkMode, dispatcherType)
        }

        /**
         * Sometimes it is quite useful to test the benchmark on one particular configuration. In this case you can use
         * this method in fun main in RunBenchmark.
         */
        fun defaultConfiguration() : BenchmarkConfiguration {
            return BenchmarkConfiguration(4, 10000, 0.2, ChannelCreator.BUFFERED_UNLIMITED,
                    80, BenchmarkModes.CHOOSE_BASED_ON_ACTIVITY, DispatcherTypes.FORK_JOIN)
        }
    }
}

class BenchmarkResults {
    val sentMessagesPerRun = ArrayList<Double>()

    val receivedMessagesPerRun = ArrayList<Double>()

    fun toCSV() : String {
        val avgSentMessages = sentMessagesPerRun.average()
        val avgReceivedMessages = receivedMessagesPerRun.average()
        val stdSentMessages = sentMessagesPerRun.standardDeviation()
        val stdReceivedMessages = receivedMessagesPerRun.standardDeviation()
        return "%.2f,%.2f,%.2f,%.2f".format(avgSentMessages, stdSentMessages, avgReceivedMessages, stdReceivedMessages)
    }
}