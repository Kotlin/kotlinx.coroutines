package kotlinx.coroutines.experimental.scheduling

import kotlinx.coroutines.experimental.Runnable
import java.io.Closeable
import java.util.*
import java.util.concurrent.ConcurrentLinkedQueue
import java.util.concurrent.Executor
import java.util.concurrent.locks.LockSupport

/**
 * TODO design rationale
 */
class CoroutineScheduler(private val corePoolSize: Int) : Executor, Closeable {

    private val workers: Array<PoolWorker>
    private val globalWorkQueue: Queue<Task> = ConcurrentLinkedQueue<Task>()
    @Volatile
    private var isClosed = false

    init {
        require(corePoolSize >= 1, { "Expected positive core pool size, but was $corePoolSize" })
        workers = Array(corePoolSize, { PoolWorker(it) })
        workers.forEach { it.start() }
    }

    override fun execute(command: Runnable) = dispatch(command)

    override fun close() {
        isClosed = true
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

    private inner class PoolWorker(index: Int) : Thread("CoroutinesScheduler-worker-$index") {
        init {
            isDaemon = true
        }

        val localQueue: WorkQueue = WorkQueue()

        @Volatile
        var yields = 0

        override fun run() {
            while (!isClosed) {
                try {
                    val job = findTask()
                    if (job == null) {
                        awaitWork()
                    } else {
                        yields = 0
                        job.task.run()
                    }
                } catch (e: Throwable) {
                    println(e) // TODO handler
                }
            }
        }

        private fun awaitWork() {
            // Temporary solution
            if (++yields > 100000) {
                LockSupport.parkNanos(WORK_STEALING_TIME_RESOLUTION / 2)
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
                val worker = workers[RANDOM_PROVIDER().nextInt(workers.size)]
                if (worker !== this) {
                    worker.localQueue.offloadWork(true) {
                        localQueue.offer(it, globalWorkQueue)
                    }

                    return localQueue.poll()
                }
            }
        }
    }
}
