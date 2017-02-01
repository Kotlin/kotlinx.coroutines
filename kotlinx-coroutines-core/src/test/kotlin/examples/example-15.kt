package example15

import kotlinx.coroutines.experimental.*

fun main(args: Array<String>) = runBlocking<Unit> {
    val jobs = List(100_000) { // create a lot of coroutines and list their jobs
        launch(CommonPool) {
            delay(1000L)
            print(".")
        }
    }
    jobs.forEach { it.join() } // wait for all jobs to complete
}
