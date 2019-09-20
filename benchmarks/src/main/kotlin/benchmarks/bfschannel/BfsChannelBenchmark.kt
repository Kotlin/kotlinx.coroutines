/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:JvmName("BfsChannelBenchmark")

package benchmarks.bfschannel


import kotlinx.atomicfu.atomic
import kotlinx.coroutines.GlobalScope
import kotlinx.coroutines.Job
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.launch
import kotlinx.coroutines.runBlocking
import org.nield.kotlinstatistics.standardDeviation
import java.io.FileInputStream
import java.io.FileOutputStream
import java.io.InputStreamReader
import java.io.PrintWriter
import java.net.URL
import java.nio.channels.Channels
import java.nio.file.Paths
import java.util.*
import java.util.concurrent.atomic.AtomicLong
import java.util.zip.GZIPInputStream
import kotlin.collections.ArrayList

private val GRAPHS = listOf(
        RandomGraphCreator("RAND-1M-10M", 1_000_000, 10_000_000),
        GrGzGraphCreator("USA-DISTANCE", "http://www.dis.uniroma1.it/challenge9/data/USA-road-d/USA-road-d.USA.gr.gz"),
        TxtGzGraphCreator("LIVE-JOURNAL", "https://snap.stanford.edu/data/soc-LiveJournal1.txt.gz"))
/**
 * Iterations count for each graph
 */
private const val ITERATIONS = 5
/**
 * Number of coroutines that are used to execute bfs in parallel
 */
private val COROUTINES = listOf(1, 4, 8, 16)
/**
 * Output file for the benchmark results
 */
private const val RESULT_FILE = "out/resultsBfs.csv"

/**
 * This benchmark tests channel as a working queue, as a queue under contention.
 * The benchmark creates or downloads graphs, then executes parallel BFS using channel as a queue, executes sequential BFS,
 * compares the results and computes execution times.
 *
 * NB: this benchmark works painfully slow without syncronization on methods [kotlinx.coroutines.internal.LockFreeLinkedListNode.remove]
 * and [kotlinx.coroutines.internal.LockFreeLinkedListNode.helpDelete] (or other channels fixes).
 */
fun main() {
    val results = ArrayList<String>()
    for (graphCreator in GRAPHS) {
        val graphName = graphCreator.name
        println("=== $graphName ===")
        val graph = graphCreator.getGraph()

        val startNode = graph[0]

        // warmup
        val sequentialResults = runBfs(graph) { bfsSequential(startNode, graph) }

        // benchmark iterations
        val sequentialExecutionTimes = (1..ITERATIONS).map { runBfs(graph) { bfsSequential(startNode, graph) }.executionTime }

        results += "$graphName,0,${sequentialExecutionTimes.average() / 1_000_000},${sequentialExecutionTimes.standardDeviation() / 1_000_000}"

        println("sequential execution time = ${sequentialExecutionTimes.average() / 1_000_000}ms " +
                "std = ${sequentialExecutionTimes.standardDeviation() / 1_000_000}ms")

        for (coroutines in COROUTINES) {
            // warmup
            runBfs(graph) { bfsParallel(startNode, graph, coroutines) }

            // benchmark iterations
            val parallelExecutionTimes = (1..ITERATIONS).map {
                val parallelResults = runBfs(graph) { bfsParallel(startNode, graph, coroutines) }
                check(parallelResults.distances.contentEquals(sequentialResults.distances)) { "Results found using parallel and sequential bfs are not the same" }
                parallelResults.executionTime
            }

            results += "$graphName,$coroutines,${parallelExecutionTimes.average() / 1_000_000}," +
                    "${parallelExecutionTimes.standardDeviation() / 1_000_000}"
            println("coroutines count = $coroutines, " +
                    "parallel execution time = ${parallelExecutionTimes.average() / 1_000_000}ms " +
                    "std = ${parallelExecutionTimes.standardDeviation() / 1_000_000}ms")
        }
    }
    PrintWriter(RESULT_FILE).use { writer ->
        writer.println("graphName,coroutines,executionTimeAvgMs,executionTimeStdMs")
        for (result in results) {
            writer.println(result)
        }
    }
}

private inline fun runBfs(graph: List<Node>, bfsAlgo: () -> Array<Int>): ExecutionResult {
    val start = System.nanoTime()
    val distances = bfsAlgo.invoke()
    val end = System.nanoTime()
    graph.forEach { node -> node.distance.value = Int.MAX_VALUE } // clear distances
    return ExecutionResult(end - start, distances)
}

class ExecutionResult(val executionTime: Long, val distances: Array<Int>)

private fun bfsSequential(start: Node, graph: List<Node>): Array<Int> {
    // The distance to the start node is `0`
    start.distance.value = 0

    val queue = ArrayDeque<Node>()
    queue.add(start)
    while (queue.isNotEmpty()) {
        val currentNode = queue.poll()
        for (neighbourNode in currentNode.neighbours) {
            val newDistance = currentNode.distance.value + 1
            val oldDistance = neighbourNode.distance.value
            if (newDistance < oldDistance) {
                neighbourNode.distance.value = newDistance
                queue.add(neighbourNode)
            }
        }
    }
    return Array(graph.size) { graph[it].distance.value }
}

private fun bfsParallel(start: Node, graph: List<Node>, coroutines: Int): Array<Int> = runBlocking {
    // The distance to the start node is `0`
    start.distance.value = 0

    val queue: Channel<Node> = TaskChannel(coroutines)
    queue.offer(start)
    // Run worker threads and wait until the total work is done
    val workers = ArrayList<Job>()
    repeat(coroutines) {
        workers += GlobalScope.launch {
            while (true) {
                val currentNode = queue.receiveOrClosed().valueOrNull ?: break
                for (neighbourNode in currentNode.neighbours) {
                    relaxEdge(currentNode, neighbourNode, queue)
                }
            }
        }
    }
    workers.forEach { it.join() }

    // Return the result
    return@runBlocking Array(graph.size) { graph[it].distance.value }
}

private fun relaxEdge(currentNode: Node, neighbourNode: Node, queue: Channel<Node>) {
    val newDistance = currentNode.distance.value + 1
    // try to compare and set if new distance is less than the old one
    while (true) {
        val toDistance = neighbourNode.distance.value
        if (toDistance <= newDistance) return
        if (neighbourNode.distance.compareAndSet(toDistance, newDistance)) {
            queue.offer(neighbourNode)
            return
        }
    }
}

private class Node(val id: Int) {
    private val _neighbours = arrayListOf<Node>()
    val neighbours: List<Node> = _neighbours

    fun addNeighbour(node: Node) {
        _neighbours.add(node)
    }

    val distance = atomic(Int.MAX_VALUE)
}

/**
 * This channel implementation does not suspend on sends and closes itself if the number of waiting receivers exceeds [maxWaitingReceivers].
 */
@Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER", "SubscriberImplementation")
private class TaskChannel<E>(private val maxWaitingReceivers: Int) : LinkedListChannel<E>() {
    private val waitingReceivers = AtomicLong(0)

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

private abstract class GraphCreator(val name: String) {
    fun getGraph(): List<Node> {
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
    override val graphFileName = "out/$name.gr"

    override fun generateOrDownloadGraphFile(graphFileName: String) {
        println("Generating $graphFileName as a random graph with $nodes nodes and $edges edges")
        val graphNodes = randomConnectedGraph(nodes, edges)
        writeGraphToGrFile(graphFileName, graphNodes)
        println("Generated $graphFileName")
    }

    override fun parseGraphFile(graphFileName: String): List<Node> = parseGrFile(graphFileName, false)
}

private class GrGzGraphCreator(name: String, private val url: String) : GraphCreator(name) {
    override val graphFileName = "out/$name.gr.gz"

    override fun generateOrDownloadGraphFile(graphFileName: String) = downloadGraphFile(graphFileName, url)

    override fun parseGraphFile(graphFileName: String): List<Node> = parseGrFile(graphFileName, true)
}

private class TxtGzGraphCreator(name: String, private val url: String) : GraphCreator(name) {
    override val graphFileName = "out/$name.txt.gz"

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
            if (first.neighbours.any { node -> node == second }) continue
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
                pw.println("a ${from.id} ${to.id}")
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
                    line.startsWith("c ") -> {} // ignore comments
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

private fun parseTxtFile(filename: String): List<Node> {
    val nodes = ArrayList<Node>()
    val inputStream = GZIPInputStream(FileInputStream(filename))
    inputStream.use { input ->
        InputStreamReader(input).buffered().useLines {
            it.forEach { line ->
                when {
                    line.startsWith("# ") -> {} // ignore comments
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
