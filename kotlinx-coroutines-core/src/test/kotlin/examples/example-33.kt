package example33

import kotlinx.coroutines.experimental.CommonPool
import kotlinx.coroutines.experimental.delay
import kotlinx.coroutines.experimental.lazyDefer
import kotlinx.coroutines.experimental.runBlocking
import kotlin.system.measureTimeMillis

suspend fun doSomethingUsefulOne(): Int {
    delay(1000L) // pretend we are doing something useful here
    return 13
}

suspend fun doSomethingUsefulTwo(): Int {
    delay(1000L) // pretend we are doing something useful here, too
    return 29
}

fun main(args: Array<String>) = runBlocking<Unit> {
    val time = measureTimeMillis {
        val one = lazyDefer(CommonPool) { doSomethingUsefulOne() }
        val two = lazyDefer(CommonPool) { doSomethingUsefulTwo() }
        println("The answer is ${one.await() + two.await()}")
    }
    println("Completed in $time ms")
}
