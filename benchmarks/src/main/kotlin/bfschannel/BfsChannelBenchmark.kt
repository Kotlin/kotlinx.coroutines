@file:JvmName("BfsChannelBenchmark")

package bfschannel


import kotlinx.coroutines.GlobalScope
import kotlinx.coroutines.Job
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.launch
import kotlinx.coroutines.runBlocking
import org.apache.commons.math3.stat.descriptive.moment.StandardDeviation
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

private val GRAPH_FILES = listOf(
        Triple("RAND-1M-10M", "rand", "1000000 10000000"), // 1M nodes and 10M edges
        Triple("USA-DISTANCE", "gr gz", "http://www.dis.uniroma1.it/challenge9/data/USA-road-d/USA-road-d.USA.gr.gz"),
        Triple("LIVE-JOURNAL", "txt gz", "https://snap.stanford.edu/data/soc-LiveJournal1.txt.gz"))
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
private val RESULT_FILE = "src/main/kotlin/bfschannel/results.csv"

/**
 * This benchmark tests channel as a working queue, as a queue under contention.
 * The benchmark creates or downloads graphs, then executes parallel BFS using channel as a queue, executes sequential BFS,
 * compares the results and computes execution times.
 *
 * NB: this benchmark works painfully slow without syncronization on methods [kotlinx.coroutines.internal.LockFreeLinkedListNode.remove]
 * and [kotlinx.coroutines.internal.LockFreeLinkedListNode.helpDelete] (or other channels fixes).
 */
fun main() {
    val standardDeviation = StandardDeviation()
    val results = ArrayList<String>()
    for ((graphName, graphType, graphUrl) in GRAPH_FILES) {
        println("=== $graphName ===")
        val graph = downloadOrCreateAndParseGraph(graphName, graphType, graphUrl)

        val nodes = graph.size
        val startNode = graph[0]

        // warmup
        val sequentialResults = runSequentialBfs(startNode, nodes)

        // benchmark iterations
        val sequentialExecutionTimes = (1..ITERATIONS).map { runSequentialBfs(startNode, nodes).executionTime.toDouble() }.toDoubleArray()

        results += "$graphName,0,${sequentialExecutionTimes.average() / 1_000_000},${standardDeviation.evaluate(sequentialExecutionTimes) / 1_000_000}"

        for (coroutines in COROUTINES) {
            // warmup
            runParallelBfs(startNode, nodes, coroutines)

            // benchmark iterations
            val parallelExecutionTimes = (1..ITERATIONS).map {
                val parallelResults = runParallelBfs(startNode, nodes, coroutines)
                check(parallelResults.distances == sequentialResults.distances)
                parallelResults.executionTime.toDouble()
            }.toDoubleArray()

            results += "$graphName,$coroutines,${parallelExecutionTimes.average() / 1_000_000}," +
                    "${standardDeviation.evaluate(parallelExecutionTimes) / 1_000_000}"
            println("coroutines count = $coroutines, " +
                    "parallel execution time = ${parallelExecutionTimes.average() / 1_000_000}ms " +
                    "std = ${standardDeviation.evaluate(parallelExecutionTimes) / 1_000_000}ms, " +
                    "sequential execution time = ${sequentialExecutionTimes.average() / 1_000_000}ms " +
                    "std = ${standardDeviation.evaluate(sequentialExecutionTimes) / 1_000_000}ms")
        }
    }
    PrintWriter(RESULT_FILE).use { writer ->
        writer.println("graphName,coroutines,executionTimeAvgMs,executionTimeStdMs")
        for (result in results) {
            writer.println(result)
        }
    }
}

private fun runParallelBfs(startNode: Node, nodes: Int, coroutines: Int) : ExecutionResults {
    val start = System.nanoTime()
    val distances = bfsParallel(startNode, nodes, coroutines)
    val end = System.nanoTime()

    return ExecutionResults(end - start, distances)
}

private fun runSequentialBfs(startNode: Node, nodes: Int) : ExecutionResults {
    val start = System.nanoTime()
    val distances = bfsSequential(startNode, nodes)
    val end = System.nanoTime()

    return ExecutionResults(end - start, distances)
}

class ExecutionResults(val executionTime : Long, val distances : List<Long>)

fun bfsSequential(startNode: Node, nodes: Int): List<Long> {
    val distances = Array(nodes) { Long.MAX_VALUE }
    // The distance to the start node is `0`
    distances[startNode.id] = 0

    val queue = LinkedList<Node>()
    queue.add(startNode)
    while (queue.isNotEmpty()) {
        val currentNode = queue.poll()
        for (edge in currentNode.outgoingEdges) {
            val newDistance = distances[currentNode.id] + 1
            val oldDistance = distances[edge.to.id]
            if (newDistance < oldDistance) {
                distances[edge.to.id] = newDistance
                queue.add(edge.to)
            }
        }
    }
    return distances.toList()
}

fun bfsParallel(start: Node, nodes: Int, coroutines: Int): List<Long> {
    val distances = Array(nodes) { AtomicLong(Long.MAX_VALUE) }
    // The distance to the start node is `0`
    distances[start.id].set(0)

    val queue : Channel<Node> = SelfClosingChannel(coroutines)
    queue.offer(start)
    // Run worker threads and wait until the total work is done
    val jobs = ArrayList<Job>()
    repeat(coroutines) {
        jobs += GlobalScope.launch {
            while (true) {
                val currentNode = queue.receiveOrClosed().valueOrNull ?: break
                for (edge in currentNode.outgoingEdges) {
                    relaxEdge(distances, currentNode, edge.to, queue)
                }
            }
        }
    }

    runBlocking {
        for (job in jobs) {
            job.join()
        }
    }
    // Return the result
    return distances.map { long -> long.toLong() }
}

private fun relaxEdge(distances: Array<AtomicLong>, currentNode: Node, nextNode: Node, queue: Channel<Node>) {
    val newDistance = distances[currentNode.id].get() + 1
    // try to compare and set if new distance is less than the old one
    while (true) {
        val toDistance = distances[nextNode.id].get()
        if (toDistance <= newDistance) {
            return
        }
        if (distances[nextNode.id].compareAndSet(toDistance, newDistance)) {
            queue.offer(nextNode)
            return
        }
    }
}

class Node(val id: Int) {
    private val _outgoingEdges = arrayListOf<Edge>()
    val outgoingEdges: List<Edge> = _outgoingEdges

    fun addEdge(edge: Edge) {
        _outgoingEdges.add(edge)
    }
}

data class Edge(val to: Node)

/**
 * Channel that closes itself if specified amount of coroutines start waiting on receive
 */
@Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER", "SubscriberImplementation")
internal class SelfClosingChannel<E>(private val maximumEnqueuedCoroutines : Int) : LinkedListChannel<E>() {
    private val counter = AtomicLong(0)

    @Suppress("CANNOT_OVERRIDE_INVISIBLE_MEMBER")
    override fun onReceiveEnqueued() {
        val enqueuedCoroutines = counter.incrementAndGet()
        if (enqueuedCoroutines >= maximumEnqueuedCoroutines) {
            close()
        }
    }

    @Suppress("CANNOT_OVERRIDE_INVISIBLE_MEMBER")
    override fun onReceiveDequeued() {
        counter.decrementAndGet()
    }
}

fun randomConnectedGraph(nodes: Int, edges: Int): List<Node> {
    require(edges >= nodes - 1)
    // always use the same seed
    val random = Random(0)
    val nodesList = List(nodes) { Node(it + 1) }
    // generate a random connected graph with `nodes-1` edges
    createGraphStructure(nodesList, random)
    // add `edges - nodes + 1` random edges
    addEdges(edges - nodes + 1, nodes, nodesList, random)
    return nodesList
}

private fun createGraphStructure(nodesList: List<Node>, random: Random) {
    val nodesToConnect = ArrayList(nodesList)
    var currentNode = nodesToConnect.removeAt(random.nextInt(nodesToConnect.size))
    val visitedNodes = mutableSetOf(currentNode)
    // create a structure for the graph, connect all the nodes
    while (nodesToConnect.isNotEmpty()) {
        val neighbor = nodesToConnect.removeAt(random.nextInt(nodesToConnect.size))
        if (visitedNodes.add(neighbor)) {
            currentNode.addEdge(Edge(neighbor))
            neighbor.addEdge(Edge(currentNode))
        }
        currentNode = neighbor
    }
}

private fun addEdges(edgesToAdd: Int, nodes: Int, nodesList: List<Node>, random: Random) {
    repeat(edgesToAdd) {
        while (true) {
            val first = nodesList[random.nextInt(nodes)]
            val second = nodesList[random.nextInt(nodes)]
            if (first.id == second.id) continue
            if (first.outgoingEdges.any { e -> e.to == second }) continue
            first.addEdge(Edge(second))
            second.addEdge(Edge(first))
            break
        }
    }
}

fun downloadOrCreateAndParseGraph(name: String, type: String, url: String): List<Node> {
    val gz = type.endsWith("gz")
    val ext = type.split(" ")[0]
    val graphFile = "out/$name." + (if (ext == "rand") "gr" else ext) + (if (gz) ".gz" else "")
    if (!Paths.get(graphFile).toFile().exists()) {
        if (ext == "rand") {
            val parts = url.split(" ")
            val nodes = parts[0].toInt()
            val edges = parts[1].toInt()
            println("Generating $graphFile as a random graph with $nodes nodes and $edges edges")
            val graphNodes = randomConnectedGraph(nodes, edges)
            writeGeneratedGraphToGrFile(graphFile, graphNodes)
            println("Generated $graphFile")
        } else {
            println("Downloading $graphFile from $url")
            val input = Channels.newChannel(URL(url).openStream())
            val output = FileOutputStream(graphFile)
            output.channel.transferFrom(input, 0, Long.MAX_VALUE)
            println("Downloaded $graphFile")
        }
    }
    return when (ext) {
        "rand", "gr" -> parseGrFile(graphFile, gz)
        "txt" -> parseTxtFile(graphFile, gz)
        else -> error("Unknown graph type: $ext")
    }
}

fun writeGeneratedGraphToGrFile(filename: String, graphNodes: List<Node>) {
    var edges = 0
    graphNodes.forEach { node -> edges += node.outgoingEdges.size }
    PrintWriter(filename).use { pw ->
        pw.println("p sp ${graphNodes.size} $edges")
        graphNodes.forEach { from ->
            from.outgoingEdges.forEach { e ->
                pw.println("a ${from.id} ${e.to.id} 1")
            }
        }
    }
}

fun parseGrFile(filename: String, gziped: Boolean): List<Node> {
    val nodes = mutableListOf<Node>()
    val inputStream = if (gziped) GZIPInputStream(FileInputStream(filename)) else FileInputStream(filename)
    InputStreamReader(inputStream).buffered().useLines { it.forEach { line ->
        when {
            line.startsWith("c ") -> {} // just ignore
            line.startsWith("p sp ") -> {
                val n = line.split(" ")[2].toInt()
                repeat(n) { nodes.add(Node(it)) }
            }
            line.startsWith("a ") -> {
                val parts = line.split(" ")
                val from = nodes[parts[1].toInt() - 1]
                val to = nodes[parts[2].toInt() - 1]
                from.addEdge(Edge(to))
            }
        }
    }
    }
    return nodes
}

fun parseTxtFile(filename: String, gziped: Boolean): List<Node> {
    val nodes = ArrayList<Node>()
    val inputStream = if (gziped) GZIPInputStream(FileInputStream(filename)) else FileInputStream(filename)
    InputStreamReader(inputStream).buffered().useLines { it.forEach { line ->
        when {
            line.startsWith("# ") -> {} // just ignore
            else -> {
                val parts = line.split(" ", "\t")
                val from = parts[0].toInt()
                val to   = parts[1].toInt()
                while (nodes.size <= from || nodes.size <= to) nodes.add(Node(nodes.size))
                nodes[from].addEdge(Edge(nodes[to]))
            }
        }
    }
    }
    return nodes
}
