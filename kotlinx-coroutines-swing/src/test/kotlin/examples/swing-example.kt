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

import kotlinx.coroutines.experimental.runBlocking
import kotlinx.coroutines.experimental.swing.Swing
import java.text.SimpleDateFormat
import java.util.*
import java.util.concurrent.ForkJoinPool
import kotlin.coroutines.experimental.suspendCoroutine

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

fun main(args: Array<String>) = runBlocking(Swing) {
    try {
        // suspend while asynchronously making request
        val result = makeRequest()
        // example.display result in UI, here Swing dispatcher ensures that we always stay in event dispatch thread
        display(result)
    } catch (exception: Throwable) {
        // process exception
    }
}

