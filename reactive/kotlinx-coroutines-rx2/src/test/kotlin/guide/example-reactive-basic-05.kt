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
package guide.reactive.basic.example05

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.rx2.rxFlowable
import io.reactivex.schedulers.Schedulers

fun main(args: Array<String>) = runBlocking<Unit> { 
    // coroutine -- fast producer of elements in the context of the main thread
    val source = rxFlowable(context) {
        for (x in 1..5) {
            println("Sending $x ...")
            send(x) // this is a suspending function
        }
    }
    // subscribe on another thread with a slow subscriber using Rx
    source
        .observeOn(Schedulers.io(), false, 1) // specify buffer size of 1 item
        .doOnComplete { println("Complete") }
        .subscribe { x ->
            println("Received $x")
            Thread.sleep(300) // 300 ms to process each item
        }
    delay(2000) // suspend main thread for couple of seconds
}
