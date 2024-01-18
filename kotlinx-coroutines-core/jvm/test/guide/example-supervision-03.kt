// This file was automatically generated from exception-handling.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.exampleSupervision03

import kotlin.coroutines.*
import kotlinx.coroutines.*

fun main() = runBlocking {
    val handler = CoroutineExceptionHandler { _, exception -> 
        println("CoroutineExceptionHandler got $exception") 
    }
    supervisorScope {
        val child = launch(handler) {
            println("The child throws an exception")
            throw AssertionError()
        }
        println("The scope is completing")
    }
    println("The scope is completed")
}
