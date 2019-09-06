@file:JvmName("InMemoryChatBenchmark")

package benchmarks.chat

import java.io.File
import java.io.PrintWriter
import java.util.concurrent.TimeUnit
import kotlin.math.round

private val SEPARATOR = System.getProperty("file.separator")
private val CLASS_PATH = System.getProperty("java.class.path")
private val JAVA_PATH = (System.getProperty("java.home") + "${SEPARATOR}bin${SEPARATOR}java")
private const val CLASS_NAME = "benchmarks.chat.RunBenchmark"
private val jvmOptions = listOf<String>(/*"-Xmx64m", "-XX:+PrintGC"*/)

fun main() {
    val configurationsList = allConfigurations
    val executionTimeMs = configurationsList.size * (WARM_UP_ITERATIONS + ITERATIONS) * BENCHMARK_TIME_MS
    println("${configurationsList.size} benchmarks will be run, benchmarks total time is " +
            "${TimeUnit.MILLISECONDS.toMinutes(executionTimeMs)} minutes")

    val benchmarkOutputFolder = File(BENCHMARK_OUTPUT_FOLDER)
    benchmarkOutputFolder.mkdir()
    val benchmarkOutputFile = PrintWriter("$BENCHMARK_OUTPUT_FOLDER/$BENCHMARK_OUTPUT_FILE")
    val csvHeader = "threads,userCount,maxFriendsPercentage,channel,averageWork,benchmarkMode,dispatcherType,avgSentMessages,stdSentMessages,avgReceivedMessages,stdReceivedMessages"
    benchmarkOutputFile.println(csvHeader)
    benchmarkOutputFile.close()

    for ((benchmark, configuration) in configurationsList.withIndex()) {
        println("${round(benchmark / configurationsList.size.toDouble() * 10000) / 100}% done, running benchmark #${benchmark + 1} with configuration ${configuration.configurationToString()}")

        val runJavaProcessCommand = ArrayList<String>()
        runJavaProcessCommand.run {
            this.add(JAVA_PATH)
            this.addAll(jvmOptions)
            this.add("-cp")
            this.add(CLASS_PATH)
            this.add(CLASS_NAME)
            this.addAll(configuration.configurationToArgsArray())
        }

        val processBuilder = ProcessBuilder(runJavaProcessCommand)
        val process = processBuilder.inheritIO().redirectError(ProcessBuilder.Redirect.INHERIT).start()

        val exitValue = process.waitFor()
        if (exitValue != 0) {
            println("The benchmark couldn't complete properly, will end running benchmarks")
            return
        }
    }
}