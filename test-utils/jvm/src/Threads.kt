package kotlinx.coroutines.testing

import kotlinx.coroutines.*
import java.lang.Runnable

private const val WAIT_LOST_THREADS = 10_000L // 10s
private val ignoreLostThreads = mutableSetOf<String>()

fun ignoreLostThreads(vararg s: String) { ignoreLostThreads += s }

fun currentThreads(): Set<Thread> {
    var estimate = 0
    while (true) {
        estimate = estimate.coerceAtLeast(Thread.activeCount() + 1)
        val arrayOfThreads = Array<Thread?>(estimate) { null }
        val n = Thread.enumerate(arrayOfThreads)
        if (n >= estimate) {
            estimate = n + 1
            continue // retry with a better size estimate
        }
        val threads = hashSetOf<Thread>()
        for (i in 0 until n)
            threads.add(arrayOfThreads[i]!!)
        return threads
    }
}

fun List<Thread>.dumpThreads(header: String) {
    println("=== $header")
    forEach { thread ->
        println("Thread \"${thread.name}\" ${thread.state}")
        val trace = thread.stackTrace
        for (t in trace) println("\tat ${t.className}.${t.methodName}(${t.fileName}:${t.lineNumber})")
        println()
    }
    println("===")
}

class PoolThread(
    @JvmField val dispatcher: ExecutorCoroutineDispatcher, // for debugging & tests
    target: Runnable, name: String
) : Thread(target, name) {
    init {
        isDaemon = true
    }
}

fun ExecutorCoroutineDispatcher.dumpThreads(header: String) =
    currentThreads().filter { it is PoolThread && it.dispatcher == this@dumpThreads }.dumpThreads(header)

fun checkTestThreads(threadsBefore: Set<Thread>) {
    // give threads some time to shutdown
    val waitTill = System.currentTimeMillis() + WAIT_LOST_THREADS
    var diff: List<Thread>
    do {
        val threadsAfter = currentThreads()
        diff = (threadsAfter - threadsBefore).filter { thread ->
            ignoreLostThreads.none { prefix -> thread.name.startsWith(prefix) }
        }
        if (diff.isEmpty()) break
    } while (System.currentTimeMillis() <= waitTill)
    ignoreLostThreads.clear()
    if (diff.isEmpty()) return
    val message = "Lost threads ${diff.map { it.name }}"
    println("!!! $message")
    diff.dumpThreads("Dumping lost thread stack traces")
    error(message)
}
