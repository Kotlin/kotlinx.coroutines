/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package examples

import kotlinx.coroutines.*
import kotlinx.coroutines.swing.*
import java.text.*
import java.util.*
import java.util.concurrent.*
import kotlin.coroutines.*

fun log(msg: String) = println("${SimpleDateFormat("yyyyMMdd-HHmmss.sss").format(Date())} [${Thread.currentThread().name}] $msg")

suspend fun makeRequest(): String {
    log("Making request...")
    return suspendCoroutine { c ->
        ForkJoinPool.commonPool().execute {
            c.resume("Result of the request")
        }
    }
}

fun display(result: String) {
    log("Displaying result '$result'")
}

fun main(args: Array<String>) = runBlocking(Dispatchers.Swing) {
    try {
        // suspend while asynchronously making request
        val result = makeRequest()
        // example.display result in UI, here Swing dispatcher ensures that we always stay in event dispatch thread
        display(result)
    } catch (exception: Throwable) {
        // process exception
    }
}

