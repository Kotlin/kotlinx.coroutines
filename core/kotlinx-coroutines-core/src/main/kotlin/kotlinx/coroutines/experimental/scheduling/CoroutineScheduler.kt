package kotlinx.coroutines.experimental.scheduling

import kotlinx.coroutines.experimental.Runnable
import java.io.Closeable
import java.util.*
import java.util.concurrent.ConcurrentLinkedQueue
import java.util.concurrent.Executor
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.locks.LockSupport

/**
 * TODO design rationale
 */
class CoroutineScheduler(private val corePoolSize: Int) : Executor, Closeable {

    private val workers: Array<PoolWorker>
    private val globalWorkQueue = ConcurrentLinkedQueue<Task>()
    private val parkedWorkers = AtomicInteger(0)
    private val random = Random()

    @Volatile
    private var isTerminated = false

    companion object {
        private const val STEAL_ATTEMPTS = 4
        private const val MAX_SPINS = 1000L
        private const val MAX_YIELDS = 500L
        @JvmStatic
        private val MAX_PARK_TIME_NS = TimeUnit.SECONDS.toNanos(1)
        @JvmStatic
        private val MIN_PARK_TIME_NS = (WORK_STEALING_TIME_RESOLUTION_NS / 4).coerceAtLeast(10).coerceAtMost(MAX_PARK_TIME_NS)

        // Local queue 'offer' results
        private const val ADDED = -1
        private const val ADDED_WITH_OFFLOADING = 0
        private const val NOT_ADDED = 1
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
        val task = TimedTask(schedulerTimeSource.nanoTime(), command)

        val offerResult = submitToLocalQueue(task, intensive)
        if (offerResult == ADDED) {
            return
        }

        if (offerResult == NOT_ADDED) {
            globalWorkQueue.add(task)
        }

        wakeUpIdleWorker()
    }

    private fun wakeUpIdleWorker() {
        // If no threads are parked don't try to wake anyone
        val parked = parkedWorkers.get()
        if (parked == 0) {
            return
        }

        // Try to wake one worker
        repeat(STEAL_ATTEMPTS) {
            val victim = workers[random.nextInt(workers.size)]
            if (victim.isParking) {
                /*
                 * Benign data race, victim can wake up after this check, but before 'unpark' call succeeds,
                 * making first 'park' in next idle period a no-op
                 */
                LockSupport.unpark(victim)
                return
            }
        }
    }


    private fun submitToLocalQueue(task: Task, intensive: Boolean): Int {
        val worker = Thread.currentThread() as? PoolWorker ?: return NOT_ADDED
        if (intensive && worker.localQueue.bufferSize > FORKED_TASK_OFFLOAD_THRESHOLD) return NOT_ADDED
        if (worker.localQueue.offer(task, globalWorkQueue)) {
            return ADDED
        }

        return ADDED_WITH_OFFLOADING
    }

    internal inner class PoolWorker(index: Int) : Thread("CoroutinesScheduler-worker-$index") {
        init {
            isDaemon = true
        }

        val localQueue: WorkQueue = WorkQueue()
        var isParking = false

        @Volatile
        private var spins = 0L

        private var yields = 0L
        private var parkTimeNs = MIN_PARK_TIME_NS
        private var rngState = random.nextInt()

        override fun run() {
            while (!isTerminated) {
                try {
                    val job = findTask()
                    if (job == null) {
                        // Wait for a job with potential park
                        idle()
                    } else {
                        idleReset()
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

        private fun idle() {
            /*
             * Simple adaptive await of work:
             * Spin on volatile field with empty loop in hope that new work will arrive,
             * then start yielding to reduce CPU pressure, and finally start adaptive parking.
             *
             * The main idea is not to park while it's possible (otherwise throughput on asymmetric workloads suffers due to too frequent
             * park/unpark calls and delays between job submission and thread queue checking)
             */
            when {
                spins < MAX_SPINS -> ++spins
                ++yields <= MAX_YIELDS -> Thread.yield()
                else -> {
                    if (!isParking) {
                        isParking = true
                        parkedWorkers.incrementAndGet()
                    }

                    if (parkTimeNs < MAX_PARK_TIME_NS) {
                        parkTimeNs = (parkTimeNs * 1.5).toLong().coerceAtMost(MAX_PARK_TIME_NS)
                    }

                    LockSupport.parkNanos(parkTimeNs)
                }
            }
        }

        private fun idleReset() {
            if (isParking) {
                isParking = false
                parkTimeNs = MIN_PARK_TIME_NS
                parkedWorkers.decrementAndGet()
            }

            spins = 0
            yields = 0
        }

        private fun findTask(): Task? {
            // TODO probabilistic check if thread is not idle?
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

            // Probe a couple of workers
            repeat(STEAL_ATTEMPTS) {
                val worker = workers[nextInt(workers.size)]
                if (worker !== this) {
                    var stolen = false
                    worker.localQueue.offloadWork(true) {
                        stolen = true
                        localQueue.offer(it, globalWorkQueue)
                    }

                    if (stolen) {
                        return@repeat
                    }
                }
            }

            return localQueue.poll()
        }
    }
}
