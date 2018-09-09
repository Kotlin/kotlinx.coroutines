/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.sync06

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.sync.*
import kotlin.system.*
import kotlin.coroutines.experimental.*

suspend fun CoroutineScope.massiveRun(action: suspend () -> Unit) {
    val n = 100  // number of coroutines to launch
    val k = 1000 // times an action is repeated by each coroutine
    val time = measureTimeMillis {
        val jobs = List(n) {
            launch {
                repeat(k) { action() }
            }
        }
        jobs.forEach { it.join() }
    }
    println("Completed ${n * k} actions in $time ms")    
}

val mutex = Mutex()
var counter = 0

fun main(args: Array<String>) = runBlocking<Unit> {
    GlobalScope.massiveRun {
        mutex.withLock {
            counter++        
        }
    }
    println("Counter = $counter")
}
