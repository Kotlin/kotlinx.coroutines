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
package guide.reactive.operators.example04

import kotlinx.coroutines.experimental.delay
import kotlinx.coroutines.experimental.launch
import kotlinx.coroutines.experimental.reactive.consumeEach
import kotlinx.coroutines.experimental.reactive.publish
import kotlinx.coroutines.experimental.runBlocking
import org.reactivestreams.Publisher
import kotlin.coroutines.experimental.CoroutineContext

fun <T> Publisher<Publisher<T>>.merge(context: CoroutineContext) = publish<T>(context) {
  consumeEach { pub ->                 // for each publisher received on the source channel
      launch(this.context) {           // launch a child coroutine
          pub.consumeEach { send(it) } // resend all element from this publisher
      }
  }
}

fun rangeWithInterval(context: CoroutineContext, time: Long, start: Int, count: Int) = publish<Int>(context) {
    for (x in start until start + count) { 
        delay(time) // wait before sending each number
        send(x)
    }
}

fun testPub(context: CoroutineContext) = publish<Publisher<Int>>(context) {
    send(rangeWithInterval(context, 250, 1, 4)) // number 1 at 250ms, 2 at 500ms, 3 at 750ms, 4 at 1000ms 
    delay(100) // wait for 100 ms
    send(rangeWithInterval(context, 500, 11, 3)) // number 11 at 600ms, 12 at 1100ms, 13 at 1600ms
    delay(1100) // wait for 1.1s - done in 1.2 sec after start
}

fun main(args: Array<String>) = runBlocking<Unit> {
    testPub(context).merge(context).consumeEach { println(it) } // print the whole stream
}
