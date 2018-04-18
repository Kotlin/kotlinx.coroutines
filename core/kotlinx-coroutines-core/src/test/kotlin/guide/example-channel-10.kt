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

// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package guide.channel.example10

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlin.coroutines.experimental.*

fun main(args: Array<String>) = runBlocking<Unit> {
 val delayChannel = DelayChannel(delay = 100, initialDelay = 0) // create delay channel
    var nextElement = withTimeoutOrNull(1) { delayChannel.receive() }
    println("Initial element is available immediately: $nextElement") // Initial delay haven't passed yet

    nextElement = withTimeoutOrNull(50) { delayChannel.receive() } // All subsequent elements has 100ms delay
    println("Next element is not ready in 50 ms: $nextElement")

    nextElement = withTimeoutOrNull(51) { delayChannel.receive() }
    println("Next element is ready in 100 ms: $nextElement")

    // Emulate large consumption delays
    println("Consumer pause in 150ms")
    delay(150)
    // Next element is available immediately
    nextElement = withTimeoutOrNull(1) { delayChannel.receive() }
    println("Next element is available immediately after large consumer delay: $nextElement")
    // Note that the pause between `receive` calls is taken into account and next element arrives faster
    nextElement = withTimeoutOrNull(60) { delayChannel.receive() } // 60 instead of 50 to mitigate scheduler delays
    println("Next element is ready in 50ms after consumer pause in 150ms: $nextElement")

    delayChannel.cancel() // indicate that no more elements are needed
}
