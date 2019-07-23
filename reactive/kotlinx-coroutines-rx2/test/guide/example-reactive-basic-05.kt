/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide-reactive.md by Knit tool. Do not edit.
package kotlinx.coroutines.rx2.guide.basic05

import io.reactivex.schedulers.*
import kotlinx.coroutines.*
import kotlinx.coroutines.rx2.*
import kotlin.coroutines.*

fun main() = runBlocking<Unit> { 
    // coroutine -- fast producer of elements in the context of the main thread
    val source = rxFlowable {
        for (x in 1..3) {
            send(x) // this is a suspending function
            println("Sent $x") // print after successfully sent item
        }
    }
    // subscribe on another thread with a slow subscriber using Rx
    source
        .observeOn(Schedulers.io(), false, 1) // specify buffer size of 1 item
        .doOnComplete { println("Complete") }
        .subscribe { x ->
            Thread.sleep(500) // 500ms to process each item
            println("Processed $x")
        }
    delay(2000) // suspend the main thread for a few seconds
}
