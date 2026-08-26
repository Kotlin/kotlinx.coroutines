@file:OptIn(ExperimentalAtomicApi::class)

package kotlinx.coroutines.testing

import kotlinx.coroutines.*
import kotlin.concurrent.atomics.*
import kotlin.native.concurrent.*

actual class MultiplatformThread actual constructor(
    private val block: Runnable, private val name: String?
) {
    private val starting = AtomicBoolean(false)
    private val started = AtomicBoolean(false)
    private val joined = AtomicBoolean(false)
    private var worker: Worker? = null
    private val threadTaskCompleted = CountDownLatch(1)
    /** Indicates whether some thread has already taken the responsibility for cleaning up the worker */
    private val workerCleanedUp = AtomicBoolean(false)

    actual fun start() {
        if (!starting.compareAndSet(false, true)) {
            error("Cannot call start() on a MultiplatformThread which has already started")
        }
        worker = Worker.start(name = name)
        val _ = worker!!.execute(TransferMode.SAFE, {
            Runnable {
                try {
                    block.run()
                } finally {
                    threadTaskCompleted.countDown()
                }
            }
        }) { it.run() }
        started.store(true)
    }

    actual fun join() {
        if (started.load() && !joined.load()) {
            threadTaskCompleted.await()
            joined.store(true)
            if (workerCleanedUp.compareAndSet(false, true)) {
                worker!!.requestTermination().result
                worker = null
            }
        }
    }
}
