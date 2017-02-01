package example16

import kotlinx.coroutines.experimental.CommonPool
import kotlinx.coroutines.experimental.delay
import kotlinx.coroutines.experimental.launch
import kotlinx.coroutines.experimental.runBlocking

fun main(args: Array<String>) = runBlocking<Unit> {
    launch(CommonPool) {
        repeat(1000) { i ->
            println("I'm sleeping $i ...")
            delay(500L)
        }
    }
    delay(1300L) // just quit after delay
}