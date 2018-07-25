/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.quasar

import co.paralleluniverse.fibers.*
import co.paralleluniverse.strands.*
import co.paralleluniverse.strands.dataflow.*
import kotlinx.coroutines.experimental.*
import org.junit.*
import java.util.concurrent.*
import kotlin.coroutines.experimental.*

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
        expect(2) // before starting fiber
        fiber.start() // now start fiber
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