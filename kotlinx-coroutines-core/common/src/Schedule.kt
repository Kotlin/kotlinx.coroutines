package kotlinx.coroutines

import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext

suspend fun <T> scheduleAsync(
    initialDelay: Long,
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend () -> T
): Deferred<T> = coroutineScope {
    async(Dispatchers.Default + Job()) {
        delay(initialDelay)
        withContext(context) { block() }
    }
}

suspend fun scheduleWithFixedDelay(
    initialDelay: Long,
    successiveDelay: Long,
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend () -> Unit
): Job = coroutineScope {
    launch(Dispatchers.Default + Job()) {
        delay(initialDelay)
        while (isActive) {
            withContext(context) { block() }
            delay(successiveDelay)
        }
    }
}

suspend fun scheduleAtFixedRate(
    initialDelay: Long,
    period: Long,
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend () -> Unit
): Job = coroutineScope {
    launch(Dispatchers.Default + Job()) {
        delay(initialDelay)
        val start = nanoTime()
        var periodMultiplier = 1L
        while (isActive) {
            launch(context) { block() }
            delay(delayNanosToMillis(start - nanoTime()) + periodMultiplier++ * period)
        }
    }
}
