package example26

import kotlinx.coroutines.experimental.delay
import kotlinx.coroutines.experimental.runBlocking
import kotlinx.coroutines.experimental.withTimeout

fun main(args: Array<String>) = runBlocking<Unit> {
    withTimeout(1300L) {
        repeat(1000) { i ->
            println("I'm sleeping $i ...")
            delay(500L)
        }
    }
}
