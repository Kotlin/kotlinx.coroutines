/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:JvmName("BfsChannelBenchmark")

package macrobenchmarks

import benchmarks.common.*
import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.channels.Channel
import org.nield.kotlinstatistics.*
import java.io.*
import java.net.*
import java.nio.channels.*
import java.nio.file.*
import java.rmi.*
import java.rmi.registry.*
import java.rmi.server.*
import java.util.*
import java.util.zip.*
import kotlin.system.*


private val GRAPHS = listOf(
        RandomGraphCreator("RAND-1M-10M", nodes = 1_000_000, edges = 10_000_000),
        DownloadingGraphCreator("USA-DISTANCE", "http://users.diag.uniroma1.it/challenge9/data/USA-road-d/USA-road-d.W.gr.gz"),
        // !NB!: node indexes in a txt file should start at 0. Check it if you decide to change the url
        DownloadingGraphCreator("INTERNET_TOPOLOGY", "http://snap.stanford.edu/data/as-skitter.txt.gz"))
/**
 * Number of iterations for each graph
 */
private const val ITERATIONS = 3
/**
 * Number of coroutines to be used to execute bfs in parallel
 */
private val PARALLELISM = listOf(1, 2)
/**
 * Benchmark output file
 */
private const val OUTPUT = "out/results_bfs_channel.csv"
/**
 * Graphs location
 */
private const val GRAPH_LOCATION = "out/bfs-channel-benchmark"
/**
 * The RMI graph service host name
 */
private const val GRAPH_CACHE_SERVICE_HOSTNAME = "127.0.0.1"
/**
 * Port number for the RMI graph service
 */
private const val GRAPH_CACHE_SERVICE_PORT = 1099
/**
 * Name of the RMI graph service
 */
private val GRAPH_CACHE_SERVICE_NAME = GraphCacheService::class.java.simpleName
/**
 * Options for benchmark jvm instances
 */
private val JVM_OPTIONS = listOf<String>(/*"-Xmx64m", "-XX:+PrintGC"*/)


/**
 * This benchmark tests channel as a working queue, as a queue under contention.
 * The benchmark creates or downloads graphs, then executes parallel BFS using channel as a queue, executes sequential BFS,
 * compares the results and computes execution times.
 * We use graph caching service to avoid parsing the text files and creating graph objects from scratch in each benchmark.
 *
 * TODO: this benchmark works painfully slow without synchronization on methods [kotlinx.coroutines.internal.LockFreeLinkedListNode.remove]
 * (or other channels fixes).
 */
fun main() {
    // Create a new output CSV file and write the header
    Files.createDirectories(Paths.get(OUTPUT).parent)
    writeOutputHeader()
    // Set up a graph cache service
    System.setProperty("java.rmi.server.hostname", GRAPH_CACHE_SERVICE_HOSTNAME)
    val service = GraphCacheServiceImpl()
    val graphService = UnicastRemoteObject.exportObject(service, GRAPH_CACHE_SERVICE_PORT) as GraphCacheService
    val registry = LocateRegistry.createRegistry(GRAPH_CACHE_SERVICE_PORT)
    registry.rebind(GRAPH_CACHE_SERVICE_NAME, graphService)
    // Run the benchmark for each graph
    try {
        for (graphCreator in GRAPHS) {
            val graphName = graphCreator.name
            println("=== $graphName ===")
            val graph = service.getGraph(graphName)
            val startNode = graph[0]
            // Execute sequential bfs to establish a baseline for benchmarks results
            val result = executeBenchmark(graph) { bfsSequential(graph, startNode) }
            println("sequential execution time = ${result.executionTime}ms std = ${result.standardDeviation}ms")
            writeIterationResults(graphName, 0, result)
            // Execute parallel bfs on different number of coroutines
            for (parallelism in PARALLELISM) {
                val exitValue = runProcess(ParallelBfsRunner::class.java.name, JVM_OPTIONS, arrayOf(graphName, parallelism.toString()))
                if (exitValue != 0) {
                    println("The benchmark couldn't complete properly, will end running benchmarks")
                    exitProcess(1)
                }
            }
        }
    } finally {
        // We should stop the graph cache service after all the benchmarks are finished
        registry.unbind(GRAPH_CACHE_SERVICE_NAME)
        UnicastRemoteObject.unexportObject(service as GraphCacheService, true)
    }
}

private fun writeOutputHeader() {
    PrintWriter(OUTPUT).use { writer -> writer.println("graphName,parallelism,executionTimeAvgMs,executionTimeStdMs") }
}

private fun writeIterationResults(graphName: String, parallelism: Int, result: BenchmarkResult) {
    FileOutputStream(OUTPUT, true).bufferedWriter().use { writer ->
        writer.append("$graphName,$parallelism,${String.format(Locale.ROOT, "%.2f",result.executionTime)},${String.format(Locale.ROOT, "%.2f",result.standardDeviation)}\n")
    }
}

private fun executeBenchmark(graph: List<Node>, bfsAlgo: () -> Unit): BenchmarkResult {
    // warmup
    runBfs(graph, bfsAlgo)
    // benchmark iterations
    val executionTimes = (1..ITERATIONS).map { runBfs(graph, bfsAlgo) }
    val executionTime = executionTimes.average() / 1_000_000
    val standardDeviation = executionTimes.standardDeviation() / 1_000_000
    return BenchmarkResult(executionTime = executionTime, standardDeviation = standardDeviation)
}

private inline fun runBfs(graph: List<Node>, bfsAlgo: () -> Unit): Long {
    val start = System.nanoTime()
    bfsAlgo.invoke()
    val end = System.nanoTime()
    graph.forEach { node -> node.distance.value = Int.MAX_VALUE } // clear distances
    return end - start
}

private data class BenchmarkResult(val executionTime: Double, val standardDeviation: Double)

// #######################################
// # GRAPH STRUCTURE AND SEQUENTIAL ALGO #
// #######################################

class Node(val id: Int) : Serializable {
    val neighbours = arrayListOf<Int>()

    fun addNeighbour(node: Node) {
        neighbours.add(node.id)
    }

    val distance = atomic(Int.MAX_VALUE)
}

private fun bfsSequential(graph: List<Node>, start: Node) {
    // The distance to the start node is `0`
    start.distance.value = 0
    val queue = ArrayDeque<Node>()
    queue.add(start)
    while (queue.isNotEmpty()) {
        val from = queue.poll()
        for (toId in from.neighbours) {
            val to = graph[toId]
            val newDistance = from.distance.value + 1
            if (newDistance < to.distance.value) {
                to.distance.lazySet(newDistance)
                queue.add(to)
            }
        }
    }
}

// #################################
// # PARALLEL ALGORITHM AND RUNNER #
// #################################

class ParallelBfsRunner {
    companion object {
        @JvmStatic
        fun main(args: Array<String>) {
            val graphName = args[0]
            val parallelism = args[1].toInt()
            // Download graph from the graph cache service
            val registry = LocateRegistry.getRegistry(GRAPH_CACHE_SERVICE_HOSTNAME, GRAPH_CACHE_SERVICE_PORT)
            val graphService = registry.lookup(GRAPH_CACHE_SERVICE_NAME) as GraphCacheService
            val graph = graphService.getGraph(graphName)
            val startNode = graph[0]
            // Execute parallel bfs
            val result = executeBenchmark(graph) { bfsParallel(graph, startNode, parallelism) }
            println("parallelism = $parallelism, parallel execution time = ${result.executionTime}ms std = ${result.standardDeviation}ms")
            writeIterationResults(graphName, parallelism, result)
        }
    }
}

fun bfsParallel(graph: List<Node>, start: Node, parallelism: Int) = runBlocking(Dispatchers.Default) {
    // The distance to the start node is `0`
    start.distance.value = 0
    val queue: Channel<Node> = TaskChannel(parallelism)
    queue.offer(start)
    // Run worker threads and wait until the total work is done
    val workers = Array(parallelism) {
        GlobalScope.launch {
            while (true) {
                val from = queue.receiveOrClosed().valueOrNull ?: break
                for (toId in from.neighbours) {
                    val to = graph[toId]
                    val newDistance = from.distance.value + 1
                    if (to.distance.updateIfLower(newDistance)) queue.offer(to)
                }
            }
        }
    }
    workers.forEach { it.join() }
}

/**
 * Try to compare and set if new distance is less than the old one
 */
private inline fun AtomicInt.updateIfLower(distance: Int): Boolean = loop { cur ->
    if (cur <= distance) return false
    if (compareAndSet(cur, distance)) return true
}

/**
 * This channel implementation does not suspend on sends and closes itself if the number of waiting receivers exceeds [maxWaitingReceivers].
 */
@Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER", "SubscriberImplementation")
private class TaskChannel<E>(private val maxWaitingReceivers: Int) : LinkedListChannel<E>() {
    private val waitingReceivers = atomic(0)

    @Suppress("CANNOT_OVERRIDE_INVISIBLE_MEMBER")
    override fun onReceiveEnqueued() {
        val waitingReceivers = waitingReceivers.incrementAndGet()
        if (waitingReceivers >= maxWaitingReceivers) close()
    }

    @Suppress("CANNOT_OVERRIDE_INVISIBLE_MEMBER")
    override fun onReceiveDequeued() {
        waitingReceivers.decrementAndGet()
    }
}

// ###################################
// # GRAPHS CREATION AND DOWNLOADING #
// ###################################

private abstract class GraphCreator(val name: String) {
    protected abstract val graphFileName: String
    protected abstract fun generateOrDownloadGraphFile()
    protected abstract fun parseGraphFile(): List<Node>

    fun getGraph(): List<Node> {
        Files.createDirectories(Paths.get(graphFileName).parent)
        if (!Paths.get(graphFileName).toFile().exists())
            generateOrDownloadGraphFile()
        return parseGraphFile()
    }
}

private class RandomGraphCreator(name: String, private val nodes: Int, private val edges: Int) : GraphCreator(name) {
    override val graphFileName = "$GRAPH_LOCATION/$name.gr"

    override fun generateOrDownloadGraphFile() {
        println("Generating $graphFileName as a random graph with $nodes nodes and $edges edges")
        val graphNodes = randomConnectedGraph(nodes, edges)
        writeGraphToGrFile(graphNodes)
        println("Generated $graphFileName")
    }

    private fun writeGraphToGrFile(graphNodes: List<Node>) {
        val edges = graphNodes.map { node -> node.neighbours.size }.sum()
        PrintWriter(graphFileName).use { pw ->
            pw.println("p sp ${graphNodes.size} $edges")
            graphNodes.forEach { from ->
                from.neighbours.forEach { toId ->
                    pw.println("a ${from.id + 1} ${toId + 1}")
                }
            }
        }
    }

    override fun parseGraphFile(): List<Node> = parseGrFile(graphFileName, false)
}

private class DownloadingGraphCreator(name: String, private val url: String) : GraphCreator(name) {
    private val fileExtension: String
    private val fileFormat: String
    private val gzipped: Boolean

    init {
        val filename = url.substring(url.lastIndexOf("/") + 1)
        gzipped = filename.endsWith(".gz")
        fileExtension = filename.substring(filename.replace(".gz", "").lastIndexOf(".") + 1)
        fileFormat = if (gzipped) fileExtension.substring(0, fileExtension.length - 3) else fileExtension
    }
    override val graphFileName = "$GRAPH_LOCATION/$name.$fileExtension"

    override fun generateOrDownloadGraphFile() {
        println("Downloading $graphFileName from $url")
        val input = Channels.newChannel(URL(url).openStream())
        val output = FileOutputStream(graphFileName)
        output.channel.transferFrom(input, 0, Long.MAX_VALUE)
        println("Downloaded $graphFileName")
    }

    override fun parseGraphFile(): List<Node> = when (fileFormat) {
        "txt" -> parseTxtFile(graphFileName, gzipped)
        "gr" -> parseGrFile(graphFileName, gzipped)
        else -> error("Unexpected graph format: $fileFormat")
    }
}

private fun parseGrFile(filename: String, gzipped: Boolean): List<Node> {
    val nodes = mutableListOf<Node>()
    val inputStream = if (gzipped) GZIPInputStream(FileInputStream(filename)) else FileInputStream(filename)
    inputStream.use { input ->
        InputStreamReader(input).buffered().useLines {
            it.forEach { line ->
                when {
                    line.startsWith("c") -> {} // ignore comments
                    line.startsWith("p sp ") -> {
                        val n = line.split(" ")[2].toInt()
                        repeat(n) { nodes.add(Node(it)) }
                    }
                    line.startsWith("a ") -> {
                        val parts = line.split(" ")
                        val from = nodes[parts[1].toInt() - 1]
                        val to = nodes[parts[2].toInt() - 1]
                        from.addNeighbour(to)
                    }
                    else -> error("Gr file $filename has an incorrect format `$line`")
                }
            }
        }
    }
    return nodes
}

private fun parseTxtFile(filename: String, gzipped: Boolean): List<Node> {
    val nodes = ArrayList<Node>()
    val inputStream = if (gzipped) GZIPInputStream(FileInputStream(filename)) else FileInputStream(filename)
    inputStream.use { input ->
        InputStreamReader(input).buffered().useLines {
            it.forEach { line ->
                when {
                    line.startsWith("#") -> {} // ignore comments
                    else -> {
                        val parts = line.split(" ", "\t")
                        // !NB!: node indexes in a txt file should start at 0
                        val from = parts[0].toInt()
                        val to = parts[1].toInt()
                        while (nodes.size <= from || nodes.size <= to) nodes.add(Node(nodes.size))
                        nodes[from].addNeighbour(nodes[to])
                    }
                }
            }
        }
        return nodes
    }
}

// ###########################
// # RANDOM GRAPH GENERATION #
// ###########################

private fun randomConnectedGraph(nodes: Int, edges: Int): List<Node> {
    require(edges >= nodes - 1)
    // always use the same seed
    val random = Random(0)
    val nodesList = List(nodes) { Node(it) }
    // generate a random connected graph with `nodes-1` edges
    generateTreeRandom(nodesList, random)
    // add `edges - nodes + 1` random edges
    addEdges(edges - nodes + 1, nodesList, random)
    return nodesList
}

private fun generateTreeRandom(nodesList: List<Node>, random: Random) {
    val nodesToConnect = ArrayList(nodesList)
    var currentNode = nodesToConnect.removeAt(random.nextInt(nodesToConnect.size))
    val visitedNodes = mutableSetOf(currentNode)
    // create a structure for the graph, connect all the nodes
    while (nodesToConnect.isNotEmpty()) {
        val neighbor = nodesToConnect.removeAt(random.nextInt(nodesToConnect.size))
        if (visitedNodes.add(neighbor)) {
            currentNode.addNeighbour(neighbor)
            neighbor.addNeighbour(currentNode)
        }
        currentNode = neighbor
    }
}

private fun addEdges(edgesToAdd: Int, nodesList: List<Node>, random: Random) {
    val nodes = nodesList.size
    repeat(edgesToAdd) {
        while (true) {
            val first = nodesList[random.nextInt(nodes)]
            val second = nodesList[random.nextInt(nodes - 1)].run {
                if (this == first) nodesList[nodes - 1] else this
            }
            if (first.neighbours.any { node -> node == second.id }) continue
            first.addNeighbour(second)
            second.addNeighbour(first)
            break
        }
    }
}

// ##########################
// # GRAPHS CACHING SERVICE #
// ##########################

interface GraphCacheService : Remote {
    @Throws(RemoteException::class)
    fun getGraph(graphName: String): List<Node>
}

private class GraphCacheServiceImpl : GraphCacheService {
    private val graphs = HashMap<String, List<Node>>()

    override fun getGraph(graphName: String): List<Node> = graphs.computeIfAbsent(graphName) {
        GRAPHS.find { it.name == graphName }!!.getGraph()
    }
}