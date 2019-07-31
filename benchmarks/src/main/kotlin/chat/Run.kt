@file:JvmName("InMemoryChatBenchmark")

package chat

import java.io.File
import java.nio.file.Files
import java.nio.file.Paths
import java.util.concurrent.ForkJoinTask
import kotlin.collections.ArrayList

var context = DispatcherTypes.FORK_JOIN.create(10)

val configurationsList = createBenchmarkConfigurationsList()
val jvmOptions = listOf<String>(/*"-Xmx64m", "-XX:+PrintGC"*/)

fun main() {
    println("${configurationsList.size} benchmarks will be run, benchmarks total time is " +
            "${configurationsList.size * (WARM_UP_ITERATIONS + BENCHMARK_ITERATIONS) * BENCHMARK_TIME_MS} ms")

    val benchmarkOutputFolder = File(BENCHMARK_OUTPUT_FOLDER)
    benchmarkOutputFolder.mkdir()

    val separator = System.getProperty("file.separator")
    val classpath = System.getProperty("java.class.path")
    val javaPath = (System.getProperty("java.home") + separator + "bin" + separator + "java")
    val className = "chat.RunBenchmark"

    for ((benchmark, configuration) in configurationsList.withIndex()) {
        println("Running ${benchmark + 1} benchmark with configuration ${configuration.configurationToString()}")

        val runJavaProcessCommand = ArrayList<String>()
        runJavaProcessCommand.add(javaPath)
        runJavaProcessCommand.addAll(jvmOptions)
        runJavaProcessCommand.add("-cp")
        runJavaProcessCommand.add(classpath)
        runJavaProcessCommand.add(className)
        runJavaProcessCommand.add(benchmark.toString())
        runJavaProcessCommand.addAll(configuration.toArray())

        val processBuilder = ProcessBuilder(runJavaProcessCommand)
        val process = processBuilder.inheritIO().redirectError(ProcessBuilder.Redirect.INHERIT).start()

        val exitValue = process.waitFor()
        if (exitValue != 0) {
            println("The benchmark couldn't complete properly, will end running benchmarks")
            return
        }
    }

    createOutputFile()
}

private fun createOutputFile() {
    val result = ArrayList<String>()

    // collecting all the results
    repeat(configurationsList.size) {
        val pathToOutputFolder = Paths.get(BENCHMARK_OUTPUT_FOLDER)
        try {
            val pathToFile = Paths.get("$pathToOutputFolder/$fileName${it + 1}")
            val lines = Files.lines(pathToFile)
            lines.forEach {
                result.add(it)
            }
        } catch (ignored: Exception) {
        }
    }

    // Filling the benchmark output file
    File("$BENCHMARK_OUTPUT_FOLDER/$BENCHMARK_OUTPUT_FILE").printWriter().use { out ->
        out.println(BENCHMARK_CONFIGURATION_FIELDS)
        result.forEach(out::println)
    }

    // Deleting all the intermediate files
    repeat(configurationsList.size) {
        val pathToOutputFolder = Paths.get(BENCHMARK_OUTPUT_FOLDER)
        try {
            val pathToFile = Paths.get("$pathToOutputFolder/$fileName${it + 1}")
            File(pathToFile.toString()).delete()
        } catch (ignored: Exception) {
        }
    }
}