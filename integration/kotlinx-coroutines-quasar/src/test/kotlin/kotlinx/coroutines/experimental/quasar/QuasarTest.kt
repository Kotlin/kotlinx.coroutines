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

package kotlinx.coroutines.experimental.quasar

import co.paralleluniverse.fibers.Fiber
import co.paralleluniverse.fibers.SuspendExecution
import co.paralleluniverse.strands.SuspendableCallable
import co.paralleluniverse.strands.dataflow.Val
import kotlinx.coroutines.experimental.*
import org.junit.Before
import org.junit.Test
import java.util.concurrent.TimeUnit

class QuasarTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads(
            "FiberTimedScheduler-default-fiber-pool",
            "ForkJoinPool-default-fiber-pool-worker-",
            "Timer-")
    }

    @Test
    fun testRunSuspendable() = runBlocking<Unit> {
        expect(1)
        val started = CompletableDeferred<Unit>() // Kotlin's event
        val x = Val<String>() // Quasar's data flow
        launch(coroutineContext) {
            started.await() // await Quasar's scheduler
            expect(3) // will get scheduled when runSuspendable suspends
            x.set("OK")
        }
        val result = runSuspendable(SuspendableCallable {
            expect(2)
            started.complete(Unit) // signal that we've started
            x.get(10, TimeUnit.SECONDS) // will get suspended
        })
        finish(4)
        check(result == "OK")
    }

    @Test
    fun testRunFiberBlocking() = runBlocking {
        expect(1)
        val started = CompletableDeferred<Unit>() // Kotlin's event
        val result = CompletableDeferred<String>() // result goes here
        val fiber = object : Fiber<String>() {
            @Throws(SuspendExecution::class)
            override fun run(): String {
                expect(3)
                started.complete(Unit) // signal that fiber is started
                // block fiber on suspendable await
                val value = runFiberBlocking {
                    result.await()
                }
                expect(5)
                return value
            }
        }
        fiber.start()
        expect(2)
        started.await() // wait fiber to start
        expect(4)
        result.complete("OK") // send Ok to fiber
        val answer = runSuspendable(SuspendableCallable {
            fiber.get()
        })
        finish(6)
        check(answer == "OK")
    }
}