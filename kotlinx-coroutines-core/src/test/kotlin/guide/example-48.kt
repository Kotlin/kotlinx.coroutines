// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package guide.example48

import kotlinx.coroutines.experimental.*

fun log(msg: String) = println("[${Thread.currentThread().name}] $msg")

fun main(args: Array<String>) = runBlocking(CoroutineName("main")) {
    log("Started main coroutine")
    // run two background value computations
    val v1 = defer(CommonPool + CoroutineName("v1coroutine")) {
        log("Computing v1")
        delay(500)
        252
    }
    val v2 = defer(CommonPool + CoroutineName("v2coroutine")) {
        log("Computing v2")
        delay(1000)
        6
    }
    log("The answer for v1 / v2 = ${v1.await() / v2.await()}")
}
