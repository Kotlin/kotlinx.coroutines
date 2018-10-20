/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide-reactive.md by Knit tool. Do not edit.
package kotlinx.coroutines.rx2.guide.basic03

import io.reactivex.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.reactive.*

fun main() = runBlocking<Unit> {
    val source = Flowable.range(1, 5) // a range of five numbers
        .doOnSubscribe { println("OnSubscribe") } // provide some insight
        .doOnComplete { println("OnComplete") }   // ...
        .doFinally { println("Finally") }         // ... into what's going on
    var cnt = 0 
    source.openSubscription().consume { // open channel to the source
        for (x in this) { // iterate over the channel to receive elements from it
            println(x)
            if (++cnt >= 3) break // break when 3 elements are printed
        }
        // Note: `consume` cancels the channel when this block of code is complete
    }
}
