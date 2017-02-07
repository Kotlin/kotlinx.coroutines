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

import kotlinx.coroutines.experimental.future.await
import kotlinx.coroutines.experimental.future.future
import java.util.concurrent.CompletableFuture

fun main(args: Array<String>) {
    // this example shows how easy it is to perform multiple async operations with coroutines
    val future = future {
        (1..5).map { // loops are no problem at all
            startLongAsyncOperation(it).await() // suspend while the long method is running
        }.joinToString("\n")
    }
    println("We have a long-running computation in background, let's wait for its result...")
    println(future.get())
}

fun startLongAsyncOperation(num: Int): CompletableFuture<String> =
    CompletableFuture.supplyAsync {
        Thread.sleep(1000L) // imitate some long-running computation, actually
        "$num" // and return a number converted to string
    }
