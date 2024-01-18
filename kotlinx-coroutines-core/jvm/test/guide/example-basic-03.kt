// This file was automatically generated from coroutines-basics.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.exampleBasic03

import kotlinx.coroutines.*

fun main() = runBlocking {
    doWorld()
}

suspend fun doWorld() = coroutineScope {  // this: CoroutineScope
    launch {
        delay(1000L)
        println("World!")
    }
    println("Hello")
}
