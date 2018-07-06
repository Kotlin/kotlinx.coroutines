/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.context07

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*

fun main(args: Array<String>) = runBlocking<Unit> {
    // start a coroutine to process some kind of incoming request
    val request = launch(coroutineContext) { // use the context of `runBlocking`
        // spawns CPU-intensive child job in CommonPool !!! 
        val job = launch(coroutineContext + CommonPool) {
            println("job: I am a child of the request coroutine, but with a different dispatcher")
            delay(1000)
            println("job: I will not execute this line if my parent request is cancelled")
        }
        job.join() // request completes when its sub-job completes
    }
    delay(500)
    request.cancel() // cancel processing of the request
    delay(1000) // delay a second to see what happens
    println("main: Who has survived request cancellation?")
}
