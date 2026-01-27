@file:OptIn(ExperimentalAtomicApi::class)

package kotlinx.coroutines.testing

import kotlinx.coroutines.*
import kotlin.concurrent.atomics.*
import kotlin.native.concurrent.*

actual fun assertTrueJvm(value: Boolean) = Unit


actual class ConcurrentThread actual constructor(
    private val block: Runnable, private val name: String?
) {
    private val starting = AtomicBoolean(false)
    private val started = AtomicBoolean(false)
    private val joined = AtomicBoolean(false)
    private var worker: Worker? = null
    private var future: Future<Unit>? = null

    actual fun start() {
        if (!starting.compareAndSet(false, true)) {
            throw IllegalStateException("Cannot call start() on a ConcurrentThread which has already started")
        }
        worker = Worker.start(name = name)
        future = worker!!.execute(TransferMode.SAFE, { block }) { it.run() }
        started.store(true)
    }

    actual fun join() {
        if (started.load() && !joined.load()) {
            future!!.consume { }
            worker!!.requestTermination().result
            joined.store(true)
        }
    }
}
