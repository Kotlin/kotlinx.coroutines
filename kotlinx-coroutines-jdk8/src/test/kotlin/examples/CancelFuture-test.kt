package examples

import kotlinx.coroutines.experimental.delay
import kotlinx.coroutines.experimental.future.future

fun main(args: Array<String>) {
    val f = future {
        try {
            log("Started f")
            delay(500)
            log("Slept 500 ms #1")
            delay(500)
            log("Slept 500 ms #2")
            delay(500)
            log("Slept 500 ms #3")
            delay(500)
            log("Slept 500 ms #4")
            delay(500)
            log("Slept 500 ms #5")
        } catch(e: Exception) {
            log("Aborting because of $e")
        }
    }
    Thread.sleep(1200)
    f.cancel(false)
}
