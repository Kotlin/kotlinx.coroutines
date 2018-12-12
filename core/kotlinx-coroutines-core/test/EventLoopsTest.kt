/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.channels.*
import org.junit.*
import org.junit.Test
import kotlin.test.*

/**
 * Tests event loops integration.
 * See [https://github.com/Kotlin/kotlinx.coroutines/issues/860].
 */
class EventLoopsTest : TestBase() {
    @Test
    fun testNestedRunBlocking() {
        runBlocking { // outer event loop
            // Produce string "OK"
            val ch = produce { send("OK") }
            // try receive this string in a blocking way:
            assertEquals("OK", runBlocking { ch.receive() }) // it should not hang here
        }
    }

    @Test
    fun testUnconfinedInRunBlocking() {
        var completed = false
        runBlocking {
            launch(Dispatchers.Unconfined) {
                completed = true
            }
            // should not go into runBlocking loop, but complete here
            assertTrue(completed)
        }
    }

    @Test
    fun testNestedUnconfined() {
        expect(1)
        GlobalScope.launch(Dispatchers.Unconfined) {
            expect(2)
            GlobalScope.launch(Dispatchers.Unconfined) {
                // this gets scheduled into outer unconfined loop
                expect(4)
            }
            expect(3) // ^^ executed before the above unconfined
        }
        finish(5)
    }

    @Test
    fun testEventLoopInDefaultExecutor() = runTest {
        expect(1)
        withContext(Dispatchers.Unconfined) {
            delay(1)
            assertTrue(Thread.currentThread().name.startsWith(DefaultExecutor.THREAD_NAME))
            expect(2)
            // now runBlocking inside default executor thread --> should use outer event loop
            DefaultExecutor.enqueue(Runnable {
                expect(4) // will execute when runBlocking runs loop
            })
            expect(3)
            runBlocking {
                expect(5)
            }
        }
        finish(6)
    }
}