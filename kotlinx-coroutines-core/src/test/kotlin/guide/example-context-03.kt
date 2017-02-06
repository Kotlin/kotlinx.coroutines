// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package guide.context.example03

import kotlinx.coroutines.experimental.*

fun log(msg: String) = println("[${Thread.currentThread().name}] $msg")

fun main(args: Array<String>) = runBlocking<Unit> {
    val a = defer(context) {
        log("I'm computing a piece of the answer")
        6
    }
    val b = defer(context) {
        log("I'm computing another piece of the answer")
        7
    }
    log("The answer is ${a.await() * b.await()}")
}
