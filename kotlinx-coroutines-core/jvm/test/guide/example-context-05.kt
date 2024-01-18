// This file was automatically generated from coroutine-context-and-dispatchers.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.exampleContext05

import kotlinx.coroutines.*

fun main() = runBlocking<Unit> {
    println("My job is ${coroutineContext[Job]}")
}
