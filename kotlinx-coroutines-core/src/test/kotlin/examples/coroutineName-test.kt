package examples

import kotlinx.coroutines.experimental.*

fun main(args: Array<String>) = runBlocking(Here + CoroutineName("main")) {
    log("Started main coroutine")
    // run two background value computations
    val v1 = defer(CommonPool + CoroutineName("v1")) {
        log("Computing v1 for a while")
        delay(500)
        log("Computed v1")
        19
    }
    val v2 = defer(CommonPool + CoroutineName("v2")) {
        log("Computing v2 for a while")
        delay(1000)
        log("Computed v2")
        23
    }
    log("The answer for v1 + v2 = ${v1.await() + v2.await()}")
}