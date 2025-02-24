package kotlinx.coroutines.testing

expect class CountDownLatch(initial: Int) {
    fun countDown()
    fun await()
}

expect fun CountDownLatch.await(timeout: kotlin.time.Duration): Boolean
