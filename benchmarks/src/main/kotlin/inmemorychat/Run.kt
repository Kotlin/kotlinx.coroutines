@file:JvmName("InMemoryChatBenchmark")

package inmemorychat

import java.io.File
import java.nio.file.Files
import java.nio.file.Paths
import java.util.*
import kotlin.collections.ArrayList
import kotlin.collections.HashMap

var context = DispatcherTypes.FORK_JOIN.create(10)

val propertiesList = createBenchmarkPropertiesList()

//val logger = org.slf4j.LoggerFactory.getLogger("InMemoryChatBenchmark")

fun main() {
//    logger.debug("Benchmarks count ${propertiesList.size}, benchmarks total time is ${propertiesList.size * (WARM_UP_ITERATIONS + BENCHMARK_ITERATIONS) * BENCHMARK_TIME_MS} ms")
    println("Benchmarks count ${propertiesList.size}, benchmarks total time is ${propertiesList.size * (WARM_UP_ITERATIONS + BENCHMARK_ITERATIONS) * BENCHMARK_TIME_MS} ms")

    val file = File(BENCHMARK_OUTPUT_FOLDER)
    file.mkdir()

    val separator = System.getProperty("file.separator")
    val classpath = System.getProperty("java.class.path")
    val javaPath = (System.getProperty("java.home") + separator + "bin" + separator + "java")
    val className = "inmemorychat.RunBenchmark"

    var benchmarkIteration = 0
    for (properties in propertiesList) {
        println("$benchmarkIteration benchmark iteration")
        benchmarkIteration++

        val arrayList = ArrayList<String>()
        arrayList.add(javaPath)
        arrayList.add("-verbose:gc -Xms128m -Xmx128m")
        arrayList.add("-cp")
        arrayList.add(classpath)
        arrayList.add(className)
        arrayList.add(benchmarkIteration.toString())
        arrayList.addAll(properties.toArray())

        val processBuilder = ProcessBuilder(arrayList)
        val process = processBuilder.inheritIO().start()

        process.waitFor()
    }

    val result = ArrayList<String>()

    repeat(propertiesList.size) {
        val pathToOutputFolder = Paths.get(BENCHMARK_OUTPUT_FOLDER)
        try {
            val pathToFile = Paths.get("$pathToOutputFolder/$fileName${it + 1}")
            val lines = Files.lines(pathToFile)
            lines.forEach {
                result.add(it)
            }
        }
        catch (ignored : Exception) {}
    }

    File("$BENCHMARK_OUTPUT_FOLDER/$BENCHMARK_OUTPUT_FILE").printWriter().use { out ->
        out.println(BENCHMARK_PROPERTIES_FIELDS)
        result.forEach(out::println)
    }

    repeat(propertiesList.size) {
        val pathToOutputFolder = Paths.get(BENCHMARK_OUTPUT_FOLDER)
        try {
            val pathToFile = Paths.get("$pathToOutputFolder/$fileName${it + 1}")
            File(pathToFile.toString()).delete()
        }
        catch (ignored : Exception) {}
    }
}