package kotlinx.coroutines.testing

actual typealias CountDownLatch = java.util.concurrent.CountDownLatch

actual fun CountDownLatch.await(timeout: kotlin.time.Duration): Boolean =
    await(timeout.inWholeMilliseconds, java.util.concurrent.TimeUnit.MILLISECONDS)
