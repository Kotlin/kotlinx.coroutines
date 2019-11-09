/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:JvmName("BfsChannelBenchmark")

package macrobenchmarks.channel


import kotlinx.atomicfu.atomic
import org.nield.kotlinstatistics.standardDeviation
import runProcess
import java.io.FileInputStream
import java.io.FileOutputStream
import java.io.InputStreamReader
import java.io.PrintWriter
import java.io.Serializable
import java.net.URL
import java.nio.channels.Channels
import java.nio.file.Files
import java.nio.file.Paths
import java.rmi.Remote
import java.rmi.RemoteException
import java.rmi.registry.LocateRegistry
import java.rmi.server.UnicastRemoteObject
import java.util.*
import java.util.zip.GZIPInputStream
import kotlin.collections.ArrayList
import kotlin.collections.HashMap


private val GRAPHS = listOf(
        RandomGraphCreator("RAND-1M-10M", 1_000_000, 10_000_000),
        GrGzGraphCreator("USA-DISTANCE", "http://users.diag.uniroma1.it/challenge9/data/USA-road-d/USA-road-d.W.gr.gz"),
        TxtGzGraphCreator("INTERNET_TOPOLOGY", "http://snap.stanford.edu/data/as-skitter.txt.gz"))
/**
 * Iterations count for each graph
 */
private const val ITERATIONS = 5
/**
 * Number of coroutines that are used to execute bfs in parallel
 */
private val PARALLELISM = listOf(1, 4, 8, 16)
/**
 * Output file for the benchmark results
 */
const val RESULT_FILE = "out/results_bfs_channel.csv"

/**
 * The RMI graph service host name
 */
const val hostName = "127.0.0.1"
/**
 * Port number for the RMI graph service
 */
const val port = 1099
/**
 * Name of the RMI graph service
 */
const val serviceName = "GraphService"
/**
 * Class name to run in a new jvm instance
 */
private const val CLASS_NAME = "macrobenchmarks.channel.ParallelBfsRunner"
/**
 * Options for the new jvm instance
 */
private val jvmOptions = listOf<String>(/*"-Xmx64m", "-XX:+PrintGC"*/)

/**
 * This benchmark tests channel as a working queue, as a queue under contention.
 * The benchmark creates or downloads graphs, then executes parallel BFS using channel as a queue, executes sequential BFS,
 * compares the results and computes execution times.
 *
 * NB: this benchmark works painfully slow without synchronization on methods [kotlinx.coroutines.internal.LockFreeLinkedListNode.remove]
 * and [kotlinx.coroutines.internal.LockFreeLinkedListNode.helpDelete] (or other channels fixes).
 */
fun main() {
    PrintWriter(RESULT_FILE).use { writer -> writer.println("graphName,parallelism,executionTimeAvgMs,executionTimeStdMs") }

    System.setProperty("java.rmi.server.hostname", hostName)
    val service = GraphServiceImpl()
    val graphService = UnicastRemoteObject.exportObject(service as GraphService, port) as GraphService
    val registry = LocateRegistry.createRegistry(port)
    registry.rebind(serviceName, graphService)

    for (graphCreator in GRAPHS) {
        // for each graph we should start a new jvm instance
        val graphName = graphCreator.name
        println("=== $graphName ===")
        val graph = service.getGraph(graphName)

        val startNode = graph[0]
        print("sequential ")
        val result = runIteration(graph, 0, graphName) { bfsSequential(graph, startNode) }

        FileOutputStream(RESULT_FILE, true).bufferedWriter().use { writer -> writer.append("$result\n") }

        for (parallelism in PARALLELISM) {
            val exitValue = runProcess(CLASS_NAME, jvmOptions, arrayOf(graphName, parallelism.toString()))
            if (exitValue != 0) {
                println("The benchmark couldn't complete properly, will end running benchmarks")
                registry.unbind(serviceName)
                UnicastRemoteObject.unexportObject(service as GraphService, true)
                return
            }
        }
    }

    registry.unbind(serviceName)
    UnicastRemoteObject.unexportObject(service as GraphService, true)
}

interface GraphService : Remote {
    @Throws(RemoteException::class)
    fun getGraph(graphName: String): List<Node>
}

private class GraphServiceImpl : GraphService {
    private val graphNameToCreator = HashMap<String, GraphCreator>()
    private val graphs = HashMap<String, List<Node>>()

    init {
        GRAPHS.forEach { graphCreator -> graphNameToCreator[graphCreator.name] = graphCreator }
    }

    override fun getGraph(graphName: String): List<Node> {
        return graphs.getOrElse(graphName) { graphNameToCreator[graphName]!!.getGraph() }
    }
}

fun runIteration(graph: List<Node>, parallelism : Int, graphName: String, bfsAlgo: () -> Unit): String {
    // warmup
    runBfs(graph, bfsAlgo)
    // benchmark iterations
    val executionTimes = (1..ITERATIONS).map { runBfs(graph, bfsAlgo) }
    println("execution time = ${executionTimes.average() / 1_000_000}ms " +
            "std = ${executionTimes.standardDeviation() / 1_000_000}ms")
    return "$graphName,$parallelism,${executionTimes.average() / 1_000_000},${executionTimes.standardDeviation() / 1_000_000}"
}

private inline fun runBfs(graph: List<Node>, bfsAlgo: () -> Unit): Long {
    val start = System.nanoTime()
    bfsAlgo.invoke()
    val end = System.nanoTime()
    graph.forEach { node -> node.distance.value = Int.MAX_VALUE } // clear distances
    return end - start
}

private fun bfsSequential(graph: List<Node>, start: Node) {
    // The distance to the start node is `0`
    start.distance.value = 0
    val queue = ArrayDeque<Node>()
    queue.add(start)
    while (queue.isNotEmpty()) {
        val currentNode = queue.poll()
        for (neighbourNodeId in currentNode.neighbours) {
            val neighbourNode = graph[neighbourNodeId - 1]
            val newDistance = currentNode.distance.value + 1
            val oldDistance = neighbourNode.distance.value
            if (newDistance < oldDistance) {
                neighbourNode.distance.lazySet(newDistance)
                queue.add(neighbourNode)
            }
        }
    }
}

class Node(val id: Int) : Serializable {
    val neighbours = arrayListOf<Int>()

    fun addNeighbour(node: Node) {
        neighbours.add(node.id)
    }

    val distance = atomic(Int.MAX_VALUE)

    companion object {
        private const val serialVersionUID: Long = 1
    }
}

private abstract class GraphCreator(val name: String) {
    fun getGraph(): List<Node> {
        Files.createDirectories(Paths.get(graphFileName).parent)
        if (!Paths.get(graphFileName).toFile().exists()) {
            generateOrDownloadGraphFile(graphFileName)
        }
        return parseGraphFile(graphFileName)
    }

    abstract val graphFileName: String

    abstract fun generateOrDownloadGraphFile(graphFileName: String)

    abstract fun parseGraphFile(graphFileName: String): List<Node>
}

private class RandomGraphCreator(name: String, private val nodes: Int, private val edges: Int) : GraphCreator(name) {
    override val graphFileName = "out/bfs-channel-benchmark/$name.gr"

    override fun generateOrDownloadGraphFile(graphFileName: String) {
        println("Generating $graphFileName as a random graph with $nodes nodes and $edges edges")
        val graphNodes = randomConnectedGraph(nodes, edges)
        writeGraphToGrFile(graphFileName, graphNodes)
        println("Generated $graphFileName")
    }

    override fun parseGraphFile(graphFileName: String): List<Node> = parseGrFile(graphFileName, false)
}

private class GrGzGraphCreator(name: String, private val url: String) : GraphCreator(name) {
    override val graphFileName = "out/bfs-channel-benchmark/$name.gr.gz"

    override fun generateOrDownloadGraphFile(graphFileName: String) = downloadGraphFile(graphFileName, url)

    override fun parseGraphFile(graphFileName: String): List<Node> = parseGrFile(graphFileName, true)
}

private class TxtGzGraphCreator(name: String, private val url: String) : GraphCreator(name) {
    override val graphFileName = "out/bfs-channel-benchmark/$name.txt.gz"

    override fun generateOrDownloadGraphFile(graphFileName: String) = downloadGraphFile(graphFileName, url)

    override fun parseGraphFile(graphFileName: String): List<Node> = parseTxtFile(graphFileName)
}

private fun downloadGraphFile(graphFileName: String, url: String) {
    println("Downloading $graphFileName from $url")
    val input = Channels.newChannel(URL(url).openStream())
    val output = FileOutputStream(graphFileName)
    output.channel.transferFrom(input, 0, Long.MAX_VALUE)
    println("Downloaded $graphFileName")
}

private fun randomConnectedGraph(nodes: Int, edges: Int): List<Node> {
    require(edges >= nodes - 1)
    // always use the same seed
    val random = Random(0)
    val nodesList = List(nodes) { Node(it + 1) }
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

private fun writeGraphToGrFile(filename: String, graphNodes: List<Node>) {
    val edges = graphNodes.map { node -> node.neighbours.size }.sum()
    PrintWriter(filename).use { pw ->
        pw.println("p sp ${graphNodes.size} $edges")
        graphNodes.forEach { from ->
            from.neighbours.forEach { to ->
                pw.println("a ${from.id} $to")
            }
        }
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
                        repeat(n) { nodes.add(Node(it + 1)) }
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

private fun parseTxtFile(filename: String): List<Node> {
    val nodes = ArrayList<Node>()
    val inputStream = GZIPInputStream(FileInputStream(filename))
    inputStream.use { input ->
        InputStreamReader(input).buffered().useLines {
            it.forEach { line ->
                when {
                    line.startsWith("#") -> {} // ignore comments
                    else -> {
                        val parts = line.split(" ", "\t")
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
