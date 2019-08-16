@file:JvmName("InMemoryChatBenchmark")

package chat

import java.io.File
import java.io.PrintWriter
import kotlin.math.round


val configurationsList = createBenchmarkConfigurationsList()
val jvmOptions = listOf<String>(/*"-Xmx64m", "-XX:+PrintGC"*/)

fun main() {
    println("${configurationsList.size} benchmarks will be run, benchmarks total time is " +
            "${configurationsList.size * (WARM_UP_ITERATIONS + BENCHMARK_ITERATIONS) * BENCHMARK_TIME_MS} ms")

    val benchmarkOutputFolder = File(BENCHMARK_OUTPUT_FOLDER)
    benchmarkOutputFolder.mkdir()
    val benchmarkOutputFile = PrintWriter("$BENCHMARK_OUTPUT_FOLDER/$BENCHMARK_OUTPUT_FILE")
    benchmarkOutputFile.println(BENCHMARK_CONFIGURATION_FIELDS)
    benchmarkOutputFile.close()

    val separator = System.getProperty("file.separator")
    val classpath = System.getProperty("java.class.path")
    val javaPath = (System.getProperty("java.home") + separator + "bin" + separator + "java")
    val className = "chat.RunBenchmark"

    for ((benchmark, configuration) in configurationsList.withIndex()) {
        println("${round(benchmark / configurationsList.size.toDouble() * 10000) / 100}%, running ${benchmark + 1} benchmark with configuration ${configuration.configurationToString()}")

        val run = ArrayList<String>()
        run.add(javaPath)
        run.addAll(jvmOptions)
        run.add("-cp")
        run.add(classpath)
        run.add(className)
        run.add(benchmark.toString())
        run.addAll(configuration.toArray())

        val processBuilder = ProcessBuilder(run)
        val process = processBuilder.inheritIO().redirectError(ProcessBuilder.Redirect.INHERIT).start()

        val exitValue = process.waitFor()
        if (exitValue != 0) {
            println("The benchmark couldn't complete properly, will end running benchmarks")
            return
        }
    }
}