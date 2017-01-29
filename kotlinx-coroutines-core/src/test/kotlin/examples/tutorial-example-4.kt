package examples

import kotlinx.coroutines.experimental.*

fun main(args: Array<String>) = runBlocking {
    val job = launch(Here) { doWorld() }
    println("Hello,")
    job.join()
}

// this is your first suspending function
suspend fun doWorld() {
    delay(1000L)
    println("World!")
}
