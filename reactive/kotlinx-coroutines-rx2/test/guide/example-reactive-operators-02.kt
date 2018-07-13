/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide-reactive.md by Knit tool. Do not edit.
package kotlinx.coroutines.rx2.guide.operators02

import kotlinx.coroutines.*
import kotlinx.coroutines.reactive.*
import org.reactivestreams.*
import kotlin.coroutines.*

fun <T, R> Publisher<T>.fusedFilterMap(
    context: CoroutineContext,   // the context to execute this coroutine in
    predicate: (T) -> Boolean,   // the filter predicate
    mapper: (T) -> R             // the mapper function
) = GlobalScope.publish<R>(context) {
    consumeEach {                // consume the source stream 
        if (predicate(it))       // filter part
            send(mapper(it))     // map part
    }        
}

fun CoroutineScope.range(start: Int, count: Int) = publish<Int> {
    for (x in start until start + count) send(x)
}

fun main(args: Array<String>) = runBlocking<Unit> {
   range(1, 5)
       .fusedFilterMap(coroutineContext, { it % 2 == 0}, { "$it is even" })
       .consumeEach { println(it) } // print all the resulting strings
}
