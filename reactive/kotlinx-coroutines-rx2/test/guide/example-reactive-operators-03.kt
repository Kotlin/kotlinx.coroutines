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
package kotlinx.coroutines.experimental.rx2.guide.operators03

import kotlinx.coroutines.experimental.channels.*
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.reactive.*
import kotlinx.coroutines.experimental.selects.*
import org.reactivestreams.*
import kotlin.coroutines.experimental.*

fun <T, U> Publisher<T>.takeUntil(context: CoroutineContext, other: Publisher<U>) = publish<T>(context) {
    this@takeUntil.openSubscription().consume { // explicitly open channel to Publisher<T>
        val current = this
        other.openSubscription().consume { // explicitly open channel to Publisher<U>
            val other = this
            whileSelect {
                other.onReceive { false }          // bail out on any received element from `other`
                current.onReceive { send(it); true }  // resend element from this channel and continue
            }
        }
    }
}

fun rangeWithInterval(context: CoroutineContext, time: Long, start: Int, count: Int) = publish<Int>(context) {
    for (x in start until start + count) { 
        delay(time) // wait before sending each number
        send(x)
    }
}

fun main(args: Array<String>) = runBlocking<Unit> {
    val slowNums = rangeWithInterval(coroutineContext, 200, 1, 10)         // numbers with 200ms interval
    val stop = rangeWithInterval(coroutineContext, 500, 1, 10)             // the first one after 500ms
    slowNums.takeUntil(coroutineContext, stop).consumeEach { println(it) } // let's test it
}
