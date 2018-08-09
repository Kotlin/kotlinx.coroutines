/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.actors02

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.actors.*
import kotlinx.coroutines.experimental.guide.sync01.*

class CountingActor : Actor() {
    
    private var counter: Int = 0
    
    override suspend fun onStart() {
      println("CountingActor started")
    }
    
    suspend fun increment() = act { // <- note act {} extension
      counter++
    }
    
    suspend fun counter(response: CompletableDeferred<Int>) = act {
          response.complete(counter)
    }
}

fun main(args: Array<String>) = runBlocking<Unit> {
    val counter = CountingActor() // create the actor
    println("Preparing to send a lot of inc requests")
    massiveRun(CommonPool) {
        counter.increment()
    }
    
    val response = CompletableDeferred<Int>()
    counter.counter(response)
    println("Counter = ${response.await()}")
    counter.close()
    counter.join() // shutdown the actor and wait for it
}
