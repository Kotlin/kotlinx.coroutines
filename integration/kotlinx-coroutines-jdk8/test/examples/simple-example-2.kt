/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.examples

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
