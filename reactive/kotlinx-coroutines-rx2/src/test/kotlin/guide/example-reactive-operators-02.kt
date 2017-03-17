/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// This file was automatically generated from coroutines-guide-reactive.md by Knit tool. Do not edit.
package guide.reactive.operators.example02

import kotlinx.coroutines.experimental.reactive.consumeEach
import kotlinx.coroutines.experimental.reactive.publish
import kotlinx.coroutines.experimental.runBlocking
import org.reactivestreams.Publisher
import kotlin.coroutines.experimental.CoroutineContext

fun <T, R> Publisher<T>.fusedFilterMap(
    context: CoroutineContext,   // the context to execute this coroutine in
    predicate: (T) -> Boolean,   // the filter predicate
    mapper: (T) -> R             // the mapper function
) = publish<R>(context) {
    consumeEach {                // consume the source stream 
        if (predicate(it))       // filter part
            send(mapper(it))     // map part
    }        
}

fun range(context: CoroutineContext, start: Int, count: Int) = publish<Int>(context) {
    for (x in start until start + count) send(x)
}

fun main(args: Array<String>) = runBlocking<Unit> {
   range(context, 1, 5)
       .fusedFilterMap(context, { it % 2 == 0}, { "$it is even" })
       .consumeEach { println(it) } // print all the resulting strings
}
