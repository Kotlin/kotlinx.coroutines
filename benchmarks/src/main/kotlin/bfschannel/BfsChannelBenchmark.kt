@file:JvmName("BfsChannelBenchmark")

package bfschannel


import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import java.io.FileInputStream
import java.io.FileOutputStream
import java.io.InputStreamReader
import java.io.PrintWriter
import java.net.URL
import java.nio.channels.Channels
import java.nio.file.Paths
import java.util.*
import java.util.concurrent.ConcurrentSkipListSet
import java.util.concurrent.atomic.AtomicLong
import java.util.zip.GZIPInputStream
import kotlin.collections.ArrayList
import kotlin.math.pow
import kotlin.math.sqrt

val GRAPH_FILES = listOf(
        Triple("RAND-1M-10M", "rand", "1000000 10000000"), // 1M nodes and 10M edges
        Triple("USA-DISTANCE", "gr gz", "http://www.dis.uniroma1.it/challenge9/data/USA-road-d/USA-road-d.USA.gr.gz"),
        Triple("LIVE-JOURNAL", "txt gz", "https://snap.stanford.edu/data/soc-LiveJournal1.txt.gz"))
/**
 * Iterations count for each graph
 */
const val GRAPH_BSF_ITERATIONS = 5
/**
 * Number of coroutines that are used to execute bfs in parallel
 */
val WORKERS = listOf(1, 4, 8, 16)

/**
 * This benchmark tests channel as a working queue, as a queue under contention.
 * The benchmark creates or downloads graphs, then executes parallel BFS using channel as a queue, executes sequential BFS,
 * compares the results and computes execution times.
 */
fun main() {
    for ((graphName, graphType, graphUrl) in GRAPH_FILES) {
        println("=== $graphName ===")
        val graph = downloadOrCreateAndParseGraph(graphName, graphType, graphUrl)

        val nodes = graph.size
        val startNode = graph[0]

        for (threads in WORKERS) {
            // warm up
            runGraphBfs(startNode, nodes, threads)

            // benchmark iterations
            val parallelExecutionTimes = ArrayList<Long>()
            val sequentialExecutionTimes = ArrayList<Long>()
            repeat(GRAPH_BSF_ITERATIONS) {
                val (parallelExecutionTime, sequentialExecutionTime) = runGraphBfs(startNode, nodes, threads)
                parallelExecutionTimes += parallelExecutionTime
                sequentialExecutionTimes += sequentialExecutionTime
            }

            println("parallel workers count = $threads, parallel execution time = ${parallelExecutionTimes.average() / 1_000_000}ms std = ${computeStandardDeviation(parallelExecutionTimes) / 1_000_000}ms, sequential execution time = ${sequentialExecutionTimes.average() / 1_000_000}ms std = ${computeStandardDeviation(sequentialExecutionTimes) / 1_000_000}ms")
        }
    }
}

fun computeStandardDeviation(list : List<Long>) : Double {
    var sum = 0.0
    var standardDeviation = 0.0
    for (num in list) {
        sum += num
    }
    val mean = sum / list.size
    for (num in list) {
        standardDeviation += (num - mean).pow(2.0)
    }
    return sqrt(standardDeviation / list.size)
}

private fun runGraphBfs(startNode: Node, nodes: Int, parallelism: Int) : Pair<Long, Long> {
    val parallelBfsStartTime = System.nanoTime()
    val parallelDistance = bfsParallel(startNode, nodes, parallelism)
    val parallelBfsEndTime = System.nanoTime()
    val sequentialDistance = bfsSequential(startNode, nodes)
    val sequentialBfsEndTime = System.nanoTime()
    check(parallelDistance == sequentialDistance)

    val parallelExecutionTime = parallelBfsEndTime - parallelBfsStartTime
    val sequentialExecutionTime = sequentialBfsEndTime - parallelBfsEndTime

    return Pair(parallelExecutionTime, sequentialExecutionTime)
}

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

fun bfsParallel(start: Node, nodes: Int, workers: Int): List<Long> {
    val distances = Array(nodes) { AtomicLong(Long.MAX_VALUE) }
    // The distance to the start node is `0`
    distances[start.id].set(0)

    val queue : Channel<Node> = UnlimitedChannel(workers)
    queue.offer(start)
    // Run worker threads and wait until the total work is done
    val jobs = ArrayList<Job>()
    val list = ConcurrentSkipListSet<Int>()
    repeat(workers) {
        jobs += GlobalScope.launch {
            while (true) {
                val currentNode = queue.receiveOrClosed().valueOrNull ?: break
                for (edge in currentNode.outgoingEdges) {
                    processEdge(distances, currentNode, edge.to, queue)
                }
                list.add(currentNode.id)
            }
        }
    }

    runBlocking {
        for (job in jobs) {
            job.join()
        }
        queue.close()
    }
    // Return the result
    return distances.map { long -> long.toLong() }
}

private fun processEdge(distances: Array<AtomicLong>, currentNode: Node, nextNode: Node, queue: Channel<Node>) {
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

@Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER", "SubscriberImplementation")
internal class UnlimitedChannel<E>(private val workers : Int) : LinkedListChannel<E>() {
    private val counter = AtomicLong(0)

    @Suppress("CANNOT_OVERRIDE_INVISIBLE_MEMBER")
    override fun onReceiveEnqueued() {
        val incrementAndGet = counter.incrementAndGet()
        if (incrementAndGet >= workers) {
            close()
        }
    }

    @Suppress("CANNOT_OVERRIDE_INVISIBLE_MEMBER")
    override fun onReceiveDequeued() {
        counter.decrementAndGet()
    }
}

data class Edge(val to: Node, val weight: Int)

fun randomConnectedGraph(nodes: Int, edges: Int, maxWeight: Int = 100): List<Node> {
    require(edges >= nodes - 1)
    // always use the same seed
    val random = Random(0)
    val nodesList = List(nodes) { Node(it + 1) }
    // generate a random connected graph with `nodes-1` edges
    createGraphStructure(nodesList, random, maxWeight)
    // add `edges - nodes + 1` random edges
    addEdges(edges - nodes + 1, nodes, nodesList, random, maxWeight)
    return nodesList
}

private fun createGraphStructure(nodesList: List<Node>, random: Random, maxWeight: Int) {
    val nodesToConnect = ArrayList(nodesList)
    var currentNode = nodesToConnect.removeAt(random.nextInt(nodesToConnect.size))
    val visitedNodes = mutableSetOf(currentNode)
    // create a structure for the graph, connect all the nodes
    while (nodesToConnect.isNotEmpty()) {
        val neighbor = nodesToConnect.removeAt(random.nextInt(nodesToConnect.size))
        if (visitedNodes.add(neighbor)) {
            val weight = random.nextInt(maxWeight)
            currentNode.addEdge(Edge(neighbor, weight))
            neighbor.addEdge(Edge(currentNode, weight))
        }
        currentNode = neighbor
    }
}

private fun addEdges(edgesToAdd: Int, nodes: Int, nodesList: List<Node>, random: Random, maxWeight: Int) {
    repeat(edgesToAdd) {
        while (true) {
            val first = nodesList[random.nextInt(nodes)]
            val second = nodesList[random.nextInt(nodes)]
            if (first.id == second.id) continue
            if (first.outgoingEdges.any { e -> e.to == second }) continue
            val weight = random.nextInt(maxWeight)
            first.addEdge(Edge(second, weight))
            second.addEdge(Edge(first, weight))
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
                pw.println("a ${from.id} ${e.to.id} ${e.weight}")
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
                val w = parts[3].toInt()
                from.addEdge(Edge(to, w))
            }
        }
    }
    }
    return nodes
}

fun parseTxtFile(filename: String, gziped: Boolean): List<Node> {
    val rand = Random(0)
    val nodes = ArrayList<Node>()
    val inputStream = if (gziped) GZIPInputStream(FileInputStream(filename)) else FileInputStream(filename)
    InputStreamReader(inputStream).buffered().useLines { it.forEach { line ->
        when {
            line.startsWith("# ") -> {} // just ignore
            else -> {
                val parts = line.split(" ", "\t")
                val from = parts[0].toInt()
                val to   = parts[1].toInt()
                val w    = rand.nextInt(100)
                while (nodes.size <= from || nodes.size <= to) nodes.add(Node(nodes.size))
                nodes[from].addEdge(Edge(nodes[to], w))
            }
        }
    }
    }
    return nodes
}
