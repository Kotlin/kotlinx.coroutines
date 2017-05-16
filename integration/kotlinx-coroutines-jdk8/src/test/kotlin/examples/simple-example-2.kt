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

package examples

import kotlinx.coroutines.experimental.delay
import kotlinx.coroutines.experimental.future.future
import java.util.concurrent.CompletableFuture
import java.util.concurrent.TimeUnit

// this function returns a CompletableFuture using Kotlin coroutines
fun supplyTheAnswerAsync(): CompletableFuture<Int> = future {
    println("We might be doing some asynchronous IO here or something else...")
    delay(1, TimeUnit.SECONDS) // just do a non-blocking delay
    42 // The answer!
}

fun main(args: Array<String>) {
    // We can use `supplyTheAnswerAsync` just like any other future-supplier function
    val future = supplyTheAnswerAsync()
    println("The answer is ${future.get()}")
}