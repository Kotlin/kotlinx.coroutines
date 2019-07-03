/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide-reactive.md by Knit tool. Do not edit.
package kotlinx.coroutines.rx2.guide.operators03

import kotlinx.coroutines.channels.*
import kotlinx.coroutines.*
import kotlinx.coroutines.reactive.*
import kotlinx.coroutines.selects.*
import org.reactivestreams.*
import kotlin.coroutines.*

fun <T, U> Publisher<T>.takeUntil(context: CoroutineContext, other: Publisher<U>) = GlobalScope.publish<T>(context) {
    this@takeUntil.openSubscription().consume { // explicitly open channel to Publisher<T>
        val current = this
        other.openSubscription().consume { // explicitly open channel to Publisher<U>
            val other = this
            whileSelect {
                other.onReceive { false }            // bail out on any received element from `other`
                current.onReceive { send(it); true } // resend element from this channel and continue
            }
        }
    }
}

fun CoroutineScope.rangeWithInterval(time: Long, start: Int, count: Int) = publish<Int> {
    for (x in start until start + count) { 
        delay(time) // wait before sending each number
        send(x)
    }
}

fun main() = runBlocking<Unit> {
    val slowNums = rangeWithInterval(200, 1, 10)         // numbers with 200ms interval
    val stop = rangeWithInterval(500, 1, 10)             // the first one after 500ms
    slowNums.takeUntil(coroutineContext, stop).collect { println(it) } // let's test it
}
