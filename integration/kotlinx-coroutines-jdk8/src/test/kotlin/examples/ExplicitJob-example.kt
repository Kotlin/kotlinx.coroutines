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

import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.delay
import kotlinx.coroutines.experimental.future.future
import java.util.concurrent.CancellationException

fun main(args: Array<String>) {
    val job = Job()
    log("Starting futures f && g")
    val f = future(job) {
        log("Started f")
        delay(500)
        log("f should not execute this line")
    }
    val g = future(job) {
        log("Started g")
        try {
            delay(500)
        } finally {
            log("g is executing finally!")
        }
        log("g should not execute this line")
    }
    log("Started futures f && g... will not wait -- cancel them!!!")
    job.cancel(CancellationException("I don't want it"))
    check(f.isCancelled)
    check(g.isCancelled)
    log("f result = ${Try<Unit> { f.get() }}")
    log("g result = ${Try<Unit> { g.get() }}")
    Thread.sleep(1000L)
    log("Nothing executed!")
}
