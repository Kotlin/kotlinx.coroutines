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
import kotlinx.coroutines.experimental.runBlocking
import java.util.concurrent.CompletableFuture

fun main(args: Array<String>) {
    // Let's assume that we have a future coming from some 3rd party API
    val future: CompletableFuture<Int> = CompletableFuture.supplyAsync {
        Thread.sleep(1000L) // imitate some long-running computation, actually
        42
    }
    // now let's launch a coroutine and await for this future inside it
    runBlocking {
        println("We can do something else, while we are waiting for future...")
        println("We've got ${future.await()} from the future!")
    }
}