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
package guide.sync.example01

import kotlinx.coroutines.experimental.*
import kotlin.system.measureTimeMillis

suspend fun massiveRun(action: suspend () -> Unit) {
    val n = 100_000
    val time = measureTimeMillis {
        val jobs = List(n) {
            launch(CommonPool) {
                action()
            }
        }
        jobs.forEach { it.join() }
    }
    println("Completed in $time ms")    
}

var counter = 0

fun main(args: Array<String>) = runBlocking<Unit> {
    massiveRun {
        counter++
    }
    println("Counter = $counter")
}
