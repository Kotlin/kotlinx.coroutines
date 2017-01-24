package examples

import kotlinx.coroutines.experimental.Here
import kotlinx.coroutines.experimental.delay
import kotlinx.coroutines.experimental.launch

fun main(args: Array<String>) {
    repeat(100_000) {
        launch(Here) { // create new coroutine without an explicit threading policy
            delay(1000L) // non-blocking delay for 1 second
            print(".") // print one dot per coroutine
        }
    }
}
