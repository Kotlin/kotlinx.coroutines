/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.basic04

import kotlinx.coroutines.*

fun main(args: Array<String>) = runBlocking { // this: CoroutineScope
    launch { 
        delay(200L)
        println("Task from runBlocking")
    }
    
    coroutineScope { // Creates a new coroutine scope
        launch {
            delay(500L) 
            println("Task from nested launch")
        }
    
        delay(100L)
        println("Task from coroutine scope") // This line will be printed before nested launch
    }
    
    println("Coroutine scope is over") // This line is not printed until nested launch completes
}
