package kotlinx.coroutines.testing

import kotlin.native.concurrent.*

actual fun assertTrueJvm(value: Boolean) = Unit

actual fun runThread(
    name: String?, block: () -> Unit
): ConcurrentThread {
    return ConcurrentThread(name, block).apply { start() }
}

actual class ConcurrentThread actual constructor(
    private val name: String?, private val block: () -> Unit
) {
    private var worker: Worker? = null
    private var future: Future<Unit>? = null

    actual fun start() {
        worker = Worker.start(name = name ?: "TestWorker")
        future = worker!!.execute(TransferMode.SAFE, { block }) {
            it()
        }
    }

    actual fun join() {
        future?.consume { }
        worker?.requestTermination()
    }
}
