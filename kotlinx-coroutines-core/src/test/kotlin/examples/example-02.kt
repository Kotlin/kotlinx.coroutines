package examples

import kotlinx.coroutines.experimental.CommonPool
import kotlinx.coroutines.experimental.delay
import kotlinx.coroutines.experimental.launch
import kotlinx.coroutines.experimental.runBlocking

fun main(args: Array<String>) = runBlocking<Unit> { // start main coroutine
    launch(CommonPool) { // create new coroutine in common thread pool
        delay(1000L)
        println("World!")
    }
    println("Hello,") // main coroutine continues while child is delayed
    delay(2000L) // non-blocking delay for 2 seconds to keep JVM alive
}
