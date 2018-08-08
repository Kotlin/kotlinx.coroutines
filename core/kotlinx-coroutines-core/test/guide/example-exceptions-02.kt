/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.exceptions02

import kotlinx.coroutines.experimental.*

fun main(args: Array<String>) = runBlocking {
    val handler = CoroutineExceptionHandler { _, exception -> println("Caught $exception") }

    val job = launch(handler) {
        throw AssertionError()
    }

    val deferred = async(handler) {
        throw ArithmeticException() // Nothing will be printed, relying on user to call deferred.await()
    }

    joinAll(job, deferred)
}
