@file:OptIn(ExperimentalAtomicApi::class)

package kotlinx.coroutines.debug

import kotlinx.coroutines.*
import java.util.TreeMap
import java.util.concurrent.*
import kotlin.concurrent.atomics.AtomicInt
import kotlin.concurrent.atomics.ExperimentalAtomicApi

/**
 * Run [invocation] in a separate thread with the given timeout in ms, after which the coroutines info is dumped and, if
 * [cancelOnTimeout] is set, the execution is interrupted.
 *
 * Assumes that [DebugProbes] are installed. Does not deinstall them.
 */
internal inline fun <T> runWithTimeoutDumpingCoroutines(
    methodName: String,
    testTimeoutMs: Long,
    cancelOnTimeout: Boolean,
    initCancellationException: () -> Throwable,
    crossinline invocation: () -> T
): T {
    val testStartedLatch = CountDownLatch(1)
    val fakeDelayEventQueue = if (fakeDelaysRequestsFromTests.load() != 0) {
        fakeDelayEventQueue.also {
            it.signalStart()
        }
    } else {
        null
    }
    val testResult = FutureTask {
        testStartedLatch.countDown()
        try {
            invocation()
        } finally {
            fakeDelayEventQueue?.signalCompletion()
        }
    }
    /*
     * We are using hand-rolled thread instead of single thread executor
     * in order to be able to safely interrupt thread in the end of a test
     */
    val testThread = Thread(testResult, "Timeout test thread").apply { isDaemon = true }
    try {
        testThread.start()
        // Await until test is started to take only test execution time into account
        testStartedLatch.await()
        return if (fakeDelayEventQueue != null) {
            fakeDelayEventQueue.processEventQueueAndAwaitCompletion(testTimeoutMs)
            testResult.get()
        } else {
            testResult.get(testTimeoutMs, TimeUnit.MILLISECONDS)
        }
    } catch (_: TimeoutException) {
        handleTimeout(testThread, methodName, testTimeoutMs, cancelOnTimeout, initCancellationException())
    } catch (e: ExecutionException) {
        throw e.cause ?: e
    }
}

private fun handleTimeout(testThread: Thread, methodName: String, testTimeoutMs: Long, cancelOnTimeout: Boolean,
                          cancellationException: Throwable): Nothing {
    val units =
        if (testTimeoutMs % 1000 == 0L)
            "${testTimeoutMs / 1000} seconds"
        else "$testTimeoutMs milliseconds"

    System.err.println("\nTest $methodName timed out after $units\n")
    System.err.flush()

    DebugProbes.dumpCoroutines()
    System.out.flush() // Synchronize serr/sout

    /*
     * Order is important:
     * 1) Create exception with a stacktrace of hang test
     * 2) Cancel all coroutines via debug agent API (changing system state!)
     * 3) Throw created exception
     */
    cancellationException.attachStacktraceFrom(testThread)
    testThread.interrupt()
    cancelIfNecessary(cancelOnTimeout)
    // If timed out test throws an exception, we can't do much except ignoring it
    throw cancellationException
}

private fun cancelIfNecessary(cancelOnTimeout: Boolean) {
    if (cancelOnTimeout) {
        DebugProbes.dumpCoroutinesInfo().forEach {
            it.job?.cancel()
        }
    }
}

private fun Throwable.attachStacktraceFrom(thread: Thread) {
    val stackTrace = thread.stackTrace
    this.stackTrace = stackTrace
}

// Testing facilities /////////////////////////////////////////////////////////

/**
 * Tests should be wrapped in this if they intend to use [fakeDelay].
 */
internal fun <T> withFakeDelayForTesting(block: () -> T): T {
    fakeDelaysRequestsFromTests.fetchAndAdd(1)
    try {
        return block()
    } finally {
        fakeDelaysRequestsFromTests.fetchAndAdd(-1)
    }
}

/**
 * Similar to [delay], but works with virtual time.
 *
 * Only call this if a [withFakeDelayForTesting] call is running.
 */
internal suspend fun fakeDelay(timeMillis: Long) {
    fakeDelayEventQueue.delay(timeMillis)
}

private val fakeDelayEventQueue by lazy {
    FakeDelayEventQueue()
}

private val fakeDelaysRequestsFromTests = AtomicInt(0)

@Suppress("PLATFORM_CLASS_MAPPED_TO_KOTLIN") // to access wait/notifyAll
internal class FakeDelayEventQueue {
    // methodName -> resumptionTime -> continuation to resume
    private var events: VirtualTimeState? = null

    fun processEventQueueAndAwaitCompletion(testTimeoutMs: Long) {
        while (true) {
            val (timeMs, tasks) = synchronized(this@FakeDelayEventQueue) {
                val currentEvents = events ?: return
                currentEvents.eventPriorityQueue.pollFirstEntry().also {
                    if (it == null) {
                        (this@FakeDelayEventQueue as Object).wait()
                        continue
                    }
                }
            }
            if (timeMs > testTimeoutMs) {
                throw TimeoutException()
            }
            for (task in tasks) {
                task.resumeWith(Result.success(Unit))
            }
            synchronized(this@FakeDelayEventQueue) {
                val currentEvents = events ?: continue
                currentEvents.currentTime = maxOf(currentEvents.currentTime, timeMs)
            }
        }
    }

    fun signalStart() {
        synchronized(this@FakeDelayEventQueue) {
            while (events != null) {
                (this@FakeDelayEventQueue as Object).wait()
            }
            events = VirtualTimeState(0, TreeMap())
        }
    }

    fun signalCompletion() {
        synchronized(this@FakeDelayEventQueue) {
            events = null
            (this@FakeDelayEventQueue as Object).notifyAll()
        }
    }

    suspend fun delay(timeMillis: Long): Unit = suspendCancellableCoroutine { cont ->
        synchronized(this@FakeDelayEventQueue) {
            val currentEvents = events ?: throw IllegalStateException(
                "Use 'withFakeDelayForTests' to allow calling the 'fakeDelay' method " +
                "and make sure a timeout is installed"
            )
            currentEvents.eventPriorityQueue.getOrPut(
                currentEvents.currentTime + timeMillis
            ) { mutableListOf() }.add(cont)
            (this@FakeDelayEventQueue as Object).notifyAll()
        }
    }

    private class VirtualTimeState(
        var currentTime: Long,
        val eventPriorityQueue: TreeMap<Long, MutableList<CancellableContinuation<Unit>>>,
    )
}
