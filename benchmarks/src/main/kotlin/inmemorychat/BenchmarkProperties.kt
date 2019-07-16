package inmemorychat

import kotlinx.coroutines.CoroutineDispatcher
import kotlinx.coroutines.asCoroutineDispatcher
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.scheduling.ExperimentalCoroutineDispatcher
import java.util.concurrent.ForkJoinPool
import kotlin.collections.ArrayList

// Benchmarks properties to monitor

/**
 * Underlying thread pool size for coroutines.
 */
val THREADS = listOf(1, 4, 8, 16)
/**
 * Chat users count.
 */
val USER_COUNT = listOf(10000)
/**
 * Maximum percentage of all chat users a user can be friends with.
 */
val MAX_FRIENDS_PERCENTAGE = listOf(0.2)
/**
 * Coroutines channels type.
 */
val CHANNEL_TYPES = listOf(ChannelType.RENDEZVOUS, ChannelType.UNLIMITED, ChannelType.BUFFERED_DEFAULT, ChannelType.BUFFERED_1, ChannelType.BUFFERED_16, ChannelType.BUFFERED_256)
/**
 * The average amount work that will be executed on CPU.
 */
val AVERAGE_WORK = listOf(40, 80)
/**
 * Implementations of users that contain different ways to produce message flow and different ways to use coroutines channels.
 */
val BENCHMARK_MODE = listOf(BenchmarkModes.USER_WITH_ONE_JOB, BenchmarkModes.USER_WITH_TWO_JOBS, BenchmarkModes.USER_WITH_SELECT)
/**
 * Coroutines dispatcher types
 */
val DISPATCHER_TYPES = listOf(DispatcherTypes.FORK_JOIN, DispatcherTypes.EXPERIMENTAL)

// Benchmark properties that are not shown in the output file

/**
 * Execution time of each benchmark.
 */
const val BENCHMARK_TIME_MS = 2000L
/**
 * Warm up iterations count
 */
const val WARM_UP_ITERATIONS = 5
/**
 * Benchmark iterations count
 */
const val BENCHMARK_ITERATIONS = 5
/**
 * Number of threads that generate commands to users to send a message
 */
const val LOADER_THREADS_COUNT = 10
/**
 * CSV file containing the configurations and final metrics of the executed benchmarks
 */
const val BENCHMARK_OUTPUT_FILE = "results.csv"
/**
 * Folder containing all benchmark output files
 */
const val BENCHMARK_OUTPUT_FOLDER = "src/main/kotlin/inmemorychat/benchmarkresults/"
/**
 * The header for the output CSV file. It should be coordinated with [inmemorychat.BenchmarkProperties.toCSV] method.
 */
const val BENCHMARK_PROPERTIES_FIELDS = "threads,userCount,maxFriendsPercentage,channelType,tokens,benchmarkMode,dispatcherType,avgSentMessages,avgReceivedMessages"

/**
 * Class containing all the benchmark properties and metrics of the run benchmark
 */
class BenchmarkProperties(
        var threads: Int = 10,
        var userCount: Int = 1000,
        var maxFriendsPercentage: Double = 0.2,
        var channelType: ChannelType = ChannelType.RENDEZVOUS,
        var tokens: Int = 80,
        var benchmarkMode: BenchmarkModes = BenchmarkModes.USER_WITH_TWO_JOBS,
        var dispatcherType: DispatcherTypes = DispatcherTypes.FORK_JOIN
) {
    val sentMessagesPerRun = ArrayList<Long>()

    val receivedMessagesPerRun = ArrayList<Long>()

    override fun toString(): String {
        return "BenchmarkProperties(threads=$threads, userCount=$userCount, maxFriendsPercentage=$maxFriendsPercentage, channelType=$channelType, tokens=$tokens, benchmarkMode=$benchmarkMode, dispatcherType=$dispatcherType, sentMessagesPerRun=$sentMessagesPerRun, receivedMessagesPerRun=$receivedMessagesPerRun)"
    }

    fun toCSV(): String {
        val avgSentMessages = sentMessagesPerRun.sum() / sentMessagesPerRun.size.toDouble()
        val avgReceivedMessages = receivedMessagesPerRun.sum() / receivedMessagesPerRun.size.toDouble()
        return "$threads,$userCount,$maxFriendsPercentage,$channelType,$tokens,$benchmarkMode,$dispatcherType,$avgSentMessages,$avgReceivedMessages"
    }

    fun toArray() : Array<String> {
        return arrayOf(threads.toString(), userCount.toString(), maxFriendsPercentage.toString(), channelType.toString(), tokens.toString(), benchmarkMode.toString())
    }

    companion object {
        fun parseArray(array : Array<String>) : BenchmarkProperties {
            return BenchmarkProperties(array[0].toInt(), array[1].toInt(), array[2].toDouble(), ChannelType.valueOf(array[3]), array[4].toInt(), BenchmarkModes.valueOf(array[5]))
        }
    }
}

enum class BenchmarkModes {
    USER_WITH_ONE_JOB,
    USER_WITH_TWO_JOBS,
    USER_WITH_SELECT
}

enum class ChannelType {
    RENDEZVOUS {
        override fun <T> createChannel(): Channel<T> {
            return Channel(Channel.RENDEZVOUS)
        }
    },
    UNLIMITED {
        override fun <T> createChannel(): Channel<T> {
            return Channel(Channel.UNLIMITED)
        }
    },
    BUFFERED_DEFAULT {
        override fun <T> createChannel(): Channel<T> {
            return Channel(Channel.BUFFERED)
        }
    },
    BUFFERED_1 {
        override fun <T> createChannel(): Channel<T> {
            return Channel(1)
        }
    },
    BUFFERED_16 {
        override fun <T> createChannel(): Channel<T> {
            return Channel(16)
        }
    },
    BUFFERED_256 {
        override fun <T> createChannel(): Channel<T> {
            return Channel(256)
        }
    };

    abstract fun <T> createChannel() : Channel<T>
}

enum class DispatcherTypes(val create: (parallelism: Int) -> CoroutineDispatcher) {
    FORK_JOIN({ parallelism -> ForkJoinPool(parallelism).asCoroutineDispatcher() }),
    EXPERIMENTAL({ parallelism -> ExperimentalCoroutineDispatcher(corePoolSize = parallelism, maxPoolSize = parallelism) })
}

fun createBenchmarkPropertiesList() : List<BenchmarkProperties> {
    val list = ArrayList<BenchmarkProperties>()
    for (threads in THREADS) {
        for (userCount in USER_COUNT) {
            for (maxFriendsPercentage in MAX_FRIENDS_PERCENTAGE) {
                for (channelType in CHANNEL_TYPES) {
                    for (tokens in AVERAGE_WORK) {
                        for (userType in BENCHMARK_MODE) {
                            for (dispatcherType in DISPATCHER_TYPES) {
                                list.add(
                                        BenchmarkProperties(
                                                threads,
                                                userCount,
                                                maxFriendsPercentage,
                                                channelType,
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