/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:JvmName("ParallelBfsRunner")

package macrobenchmarks.channel

import kotlinx.atomicfu.AtomicInt
import kotlinx.atomicfu.loop
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.GlobalScope
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.launch
import kotlinx.coroutines.runBlocking
import java.io.FileOutputStream
import java.rmi.registry.LocateRegistry
import java.util.concurrent.atomic.AtomicLong


fun main(args: Array<String>) {
    val graphName = args[0]
    val parallelism = args[1].toInt()

    val registry = LocateRegistry.getRegistry(hostName, port)
    val graphService = registry.lookup(serviceName) as GraphService
    val graph = graphService.getGraph(graphName)

    val startNode = graph[0]

    print("coroutines count = $parallelism, parallel ")
    val result = runIteration(graph, parallelism, graphName) { bfsParallel(graph, startNode, parallelism) }

    FileOutputStream(RESULT_FILE, true).bufferedWriter().use { writer -> writer.append("$result\n") }
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
                val u = queue.receiveOrClosed().valueOrNull ?: break
                for (v in u.neighbours) {
                    val node = graph[v - 1]
                    val newDistance = u.distance.value + 1
                    if (node.distance.updateIfLower(newDistance)) queue.offer(node)
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