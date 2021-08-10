/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package macrobenchmarks.chat

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.scheduling.*
import org.nield.kotlinstatistics.*
import java.util.*
import kotlin.collections.ArrayList

/**
 * Execution time of each benchmark.
 */
public const val BENCHMARK_TIME_MS: Long = 5_000L
/**
 * Warm up iterations count
 */
public const val WARM_UP_ITERATIONS: Int = 3
/**
 * Benchmark iterations count
 */
public const val ITERATIONS: Int = 20
/**
 * CSV file containing the configurations and final metrics of the executed benchmarks
 */
public const val BENCHMARK_OUTPUT_FILE: String = "out/results_in_memory_chat.csv"

// Configurations we want to test in the benchmark

/**
 * Underlying thread pool size for coroutines.
 */
//private val THREADS = listOf(12)
private val THREADS = listOf(1, 4, 8, 16, 32, 64, 128, 144)
/**
 * Chat users count.
 */
private val USER_COUNT = listOf(1_000, 10_000)
/**
 * Maximum percentage of all chat users a user can be friends with.
 */
private val MAX_FRIENDS_PERCENTAGE = listOf(0.1, 0.2, 0.5)
/**
 * The average amount work that will be executed on CPU.
 */
private val AVERAGE_WORK = listOf(100)

public enum class ChannelCreator(public val create: () -> Channel<Message?>) {
    KOTLIN_RENDEZVOUS({ Channel(Channel.RENDEZVOUS) } ),
    KOTLIN_BUFFERED_64({ Channel(64) } ),
    KOVAL_RENDEZVOUS({ kotlinx.coroutines.channels.koval_europar.RendezvousChannelEuropar() } ),
    BUFFERED_RENDEZVOUS({ BufferedChannel(Channel.RENDEZVOUS) } ),
    BUFFERED_BUFFERED_64({ BufferedChannel(64) } )
}

public enum class DispatcherTypes(public val create: (parallelism: Int) -> CoroutineDispatcher) {
//    ForkJoin({ parallelism -> ForkJoinPool(parallelism).asCoroutineDispatcher() }),
    Experimental({ parallelism -> ExperimentalCoroutineDispatcher(corePoolSize = parallelism, maxPoolSize = parallelism) })
}

public val allConfigurations: List<BenchmarkConfiguration>
    get() {
        val list = ArrayList<BenchmarkConfiguration>()
        for (threads in THREADS) {
            for (userCount in USER_COUNT) {
                for (maxFriendsPercentage in MAX_FRIENDS_PERCENTAGE) {
                    for (channelCreator in ChannelCreator.values()) {
                        for (tokens in AVERAGE_WORK) {
                            for (dispatcherType in DispatcherTypes.values()) {
                                list.add(
                                    BenchmarkConfiguration(
                                        threads,
                                        userCount,
                                        maxFriendsPercentage,
                                        channelCreator,
                                        tokens,
                                        dispatcherType
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

/**
 * Class containing all the benchmark configuration and metrics of the run benchmark
 */
public class BenchmarkConfiguration(
    public var threads: Int,
    public var users: Int,
    public var maxFriendsPercentage: Double,
    public var channelCreator: ChannelCreator,
    public var averageWork: Int,
    public var dispatcherType: DispatcherTypes
) {
    public fun configurationToString() : String {
        return "[threads=$threads, users=$users, maxFriendsPercentage=$maxFriendsPercentage, channelCreator=$channelCreator, averageWork=$averageWork, dispatcherType=$dispatcherType]"
    }

    public fun toCSV(): String {
        return "$threads,$users,$maxFriendsPercentage,$channelCreator,$averageWork,$dispatcherType"
    }

    public fun configurationToArgsArray() : Array<String> {
        return arrayOf(threads.toString(), users.toString(), maxFriendsPercentage.toString(), channelCreator.toString(), averageWork.toString(), dispatcherType.toString())
    }

    public companion object {
        public fun parseBenchmarkArgs(array : Array<String>) : BenchmarkConfiguration {
            val threads = array[0].toInt()
            val userCount = array[1].toInt()
            val maxFriendsPercentage = array[2].toDouble()
            val channelCreator = ChannelCreator.valueOf(array[3])
            val averageWork = array[4].toInt()
            val dispatcherType = DispatcherTypes.valueOf(array[5])
            return BenchmarkConfiguration(threads, userCount, maxFriendsPercentage, channelCreator, averageWork, dispatcherType)
        }
    }
}

public class BenchmarkResults {
    public val sentMessagesPerRun: java.util.ArrayList<Double> = ArrayList<Double>()

    public val receivedMessagesPerRun: java.util.ArrayList<Double> = ArrayList<Double>()

    public fun toCSV() : String {
        val avgSentMessages = sentMessagesPerRun.average()
        val avgReceivedMessages = receivedMessagesPerRun.average()
        val stdSentMessages = sentMessagesPerRun.standardDeviation()
        val stdReceivedMessages = receivedMessagesPerRun.standardDeviation()
        return String.format(Locale.ROOT, "%.2f,%.2f,%.2f,%.2f", avgSentMessages, stdSentMessages, avgReceivedMessages, stdReceivedMessages)
    }
}