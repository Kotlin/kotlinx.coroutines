package kotlinx.coroutines.testing

actual fun assertTrueJvm(value: Boolean) = kotlin.test.assertTrue(value)


actual typealias ConcurrentThread = Thread
