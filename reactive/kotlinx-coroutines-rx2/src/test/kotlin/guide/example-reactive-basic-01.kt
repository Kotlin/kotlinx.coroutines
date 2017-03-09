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
package guide.reactive.basic.example01

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*

fun main(args: Array<String>) = runBlocking<Unit> {
    // create a channel that produces numbers from 1 to 6 with 200ms delays between them
    val source = produce<Int>(context) {
        println("Begin") // mark the beginning of this coroutine in output
        for (x in 1..6) {
            delay(200) // wait for 200ms
            send(x) // send number x to the channel
        }
    }
    // print the first 3 elements from this channel
    println("First three:")
    var cnt = 0
    for (x in source) { // iterate over the source to receive elements from it
        println(x)
        if (++cnt >= 3) break // break when 3 elements are printed
    }
    // print the remaining elements from this source
    println("Remaining:")
    for (x in source) { 
        println(x)
    }
}
