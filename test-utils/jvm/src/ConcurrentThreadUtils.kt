package kotlinx.coroutines.testing

import kotlin.concurrent.*

actual fun assertTrueJvm(value: Boolean) = kotlin.test.assertTrue(value)

actual fun runThread(
    name: String?, block: () -> Unit
): ConcurrentThread = thread(block = block, name = name)

actual typealias ConcurrentThread = Thread
