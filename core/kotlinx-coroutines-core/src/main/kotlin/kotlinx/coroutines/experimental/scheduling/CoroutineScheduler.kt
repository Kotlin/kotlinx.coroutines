package kotlinx.coroutines.experimental.scheduling

import kotlinx.coroutines.experimental.Runnable
import java.io.Closeable
import java.util.*
import java.util.concurrent.ConcurrentLinkedQueue
import java.util.concurrent.Executor
import java.util.concurrent.TimeUnit
import java.util.concurrent.locks.LockSupport

/**
 * TODO design rationale
 */
class CoroutineScheduler(private val corePoolSize: Int) : Executor, Closeable {

    private val workers: Array<PoolWorker>
    private val globalWorkQueue: Queue<Task> = ConcurrentLinkedQueue<Task>()
    @Volatile
    private var isTerminated = false

    companion object {
        private const val maxSpins = 500000L
        private const val maxYields = 100000L
        @JvmStatic
        private val minParkTimeNs = WORK_STEALING_TIME_RESOLUTION_NS / 2
        @JvmStatic
        private val maxParkTimeNs = TimeUnit.SECONDS.toNanos(1)
    }

    init {
        require(corePoolSize >= 1, { "Expected positive core pool size, but was $corePoolSize" })
        workers = Array(corePoolSize, { PoolWorker(it) })
        workers.forEach { it.start() }
    }

    override fun execute(command: Runnable) = dispatch(command)

    override fun close() {
        isTerminated = true
    }

    fun dispatch(command: Runnable, intensive: Boolean = false) {
        val task = TimedTask(System.nanoTime(), command)
        if (!submitToLocalQueue(task, intensive)) {
            globalWorkQueue.add(task)
        }
    }

    private fun submitToLocalQueue(task: Task, intensive: Boolean): Boolean {
        val worker = Thread.currentThread() as? PoolWorker ?: return false
        if (intensive && worker.localQueue.bufferSize > FORKED_TASK_OFFLOAD_THRESHOLD) return false
        worker.localQueue.offer(task, globalWorkQueue)
        return true
    }

    internal inner class PoolWorker(index: Int) : Thread("CoroutinesScheduler-worker-$index") {
        init {
            isDaemon = true
        }

        val localQueue: WorkQueue = WorkQueue()

        @Volatile
        private var spins = 0L
        private var yields = 0L
        private var parks = 0L
        private var parkTimeNs = minParkTimeNs
        private var rngState = Random().nextInt()

        override fun run() {
            while (!isTerminated) {
                try {
                    val job = findTask()
                    if (job == null) {
                        awaitWork()
                    } else {
                        spins = 0
                        yields = 0
                        parkTimeNs = minParkTimeNs
                        job.task.run()
                    }
                } catch (e: Throwable) {
                    println(e) // TODO handler
                }
            }
        }

        /*
         * Marsaglia xorshift RNG with period 2^32-1 for work stealing purposes.
         * ThreadLocalRandom cannot be used to support Android and ThreadLocal<Random> is up to 15% slower on ktor benchmarks
         */
        internal fun nextInt(upperBound: Int): Int {
            rngState = rngState xor (rngState shl 13)
            rngState = rngState xor (rngState shr 17)
            rngState = rngState xor (rngState shl 5)
            val mask = upperBound - 1
            // Fast path for power of two bound
            if (mask and upperBound == 0) {
                return rngState and mask
            }

            return (rngState and Int.MAX_VALUE) % upperBound
        }

        private fun awaitWork() {
            // Temporary solution
            if (++spins <= maxSpins) {
                // Spin
            } else if (++yields <= maxYields) {
                Thread.yield()
            } else {
                ++parks
                if (parkTimeNs < maxParkTimeNs) {
                    parkTimeNs = (parkTimeNs * 1.5).toLong().coerceAtMost(maxParkTimeNs)
                }

                LockSupport.parkNanos(parkTimeNs)
            }
        }

        private fun findTask(): Task? {
            // TODO explain, probabilistic check with park counter?
            var task: Task? = globalWorkQueue.poll()
            if (task != null) return task

            task = localQueue.poll()
            if (task != null) return task

            return trySteal()
        }

        private fun trySteal(): Task? {
            if (corePoolSize == 1) {
                return null
            }

            while (true) {
                val worker = workers[nextInt(workers.size)]
                if (worker === this) {
                    continue
                }

                worker.localQueue.offloadWork(true) {
                    localQueue.offer(it, globalWorkQueue)
                }

                return localQueue.poll()
            }
        }
    }
}
