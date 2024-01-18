// This file was automatically generated from coroutines-basics.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.exampleBasic05

import kotlinx.coroutines.*

fun main() = runBlocking {
    val job = launch { // launch a new coroutine and keep a reference to its Job
        delay(1000L)
        println("World!")
    }
    println("Hello")
    job.join() // wait until child coroutine completes
    println("Done") 
}
