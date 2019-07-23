/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide-reactive.md by Knit tool. Do not edit.
package kotlinx.coroutines.rx2.guide.basic02

import kotlinx.coroutines.*
import kotlinx.coroutines.reactive.*
import kotlin.coroutines.*

fun main() = runBlocking<Unit> {
    // create a publisher that produces numbers from 1 to 3 with 200ms delays between them
    val source = publish<Int> {
    //           ^^^^^^^  <---  Difference from the previous examples is here
        println("Begin") // mark the beginning of this coroutine in output
        for (x in 1..3) {
            delay(200) // wait for 200ms
            send(x) // send number x to the channel
        }
    }
    // print elements from the source
    println("Elements:")
    source.collect { // collect elements from it
        println(it)
    }
    // print elements from the source AGAIN
    println("Again:")
    source.collect { // collect elements from it
        println(it)
    }
}
