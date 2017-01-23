package examples

import kotlinx.coroutines.experimental.CommonPool
import kotlinx.coroutines.experimental.defer
import kotlinx.coroutines.experimental.delay
import kotlinx.coroutines.experimental.future.toCompletableFuture
import java.util.concurrent.TimeUnit

fun main(args: Array<String>)  {
    log("Started")
    val deferred = defer(CommonPool) {
        log("Busy...")
        delay(1, TimeUnit.SECONDS)
        log("Done...")
        42
    }
    val future = deferred.toCompletableFuture()
    log("Got ${future.get()}")
}