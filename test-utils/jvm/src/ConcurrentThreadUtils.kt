package kotlinx.coroutines.testing

import kotlin.concurrent.*

actual fun assertTrueJvm(value: Boolean) = kotlin.test.assertTrue(value)

actual fun runThread(
    name: String?, block: () -> Unit
): ConcurrentThread {
    return ConcurrentThread(name, block).apply { start() }
}

actual class ConcurrentThread actual constructor(
    private val name: String?, private val block: () -> Unit
) {
    private var thread: Thread? = null

    actual fun start() {
        thread = thread(name = name, block = block)
    }

    actual fun join() {
        thread?.join()
    }
}
