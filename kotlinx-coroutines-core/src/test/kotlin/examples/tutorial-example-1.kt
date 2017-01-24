package examples

import kotlinx.coroutines.experimental.Here
import kotlinx.coroutines.experimental.delay
import kotlinx.coroutines.experimental.launch

fun main(args: Array<String>) {
    launch(Here) {
        delay(1000L)
        println("World!")
    }
    println("Hello!")
}