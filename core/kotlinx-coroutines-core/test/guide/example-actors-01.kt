/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.actors01

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.actors.*
import kotlinx.coroutines.experimental.guide.sync01.*

// Message types for counter actor
sealed class CounterMsg
object IncCounter : CounterMsg() // one-way message to increment counter
class GetCounter(val response: CompletableDeferred<Int>) : CounterMsg() // a request with reply

class CountingActor : TypedActor<CounterMsg>() {
    
    private var counter: Int = 0
    
     override suspend fun onStart() {
       println("CountingActor started")
     }
    
    override suspend fun receive(message: CounterMsg) {
        when (message) {
            is IncCounter -> counter++
            is GetCounter -> message.response.complete(counter)
        }
    }
}

fun main(args: Array<String>) = runBlocking<Unit> {
    val counter = CountingActor() // create the actor
    println("Preparing to send a lot of inc requests")
    massiveRun(CommonPool) {
        counter.send(IncCounter)
    }
    
    // send a message to get a counter value from an actor
    val response = CompletableDeferred<Int>()
    counter.send(GetCounter(response))
    println("Counter = ${response.await()}")
    counter.close()
    counter.join() // shutdown the actor and wait for it
}
