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

import kotlinx.coroutines.experimental.*

val receiverThread = newSingleThreadContext("ReceiverThread")

fun main(args: Array<String>) = runBlocking {
    val va = Array<Deferred<String>>(10) { i ->
        async(CommonPool) {
            val sleepTime = i * 200L
            log("This value #$i will delay for $sleepTime ms before producing result")
            try {
                delay(sleepTime)
                log("Value $i is producing result!")
            } catch (ex: Exception) {
                log("Value $i was aborted because of $ex")
            }
            "Result #$i"
        }
    }
    log("Created ${va.size} values")
    try {
        withTimeout(1100L) {
            run(receiverThread) {
                for (v in va)
                    log("Got value: ${v.await()}")
            }
        }
    } finally {
        log("The receiver thread is still active = ${receiverThread[Job.Key]!!.isActive}")
    }
}
