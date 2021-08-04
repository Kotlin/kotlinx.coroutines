/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines

import org.junit.*

class RunBlockingJvmTest : TestBase() {
    @Test
    fun testContract() {
        val rb: Int
        runBlocking {
            rb = 42
        }
        rb.hashCode() // unused
    }

    @Test
    fun testCancellation() = newFixedThreadPoolContext(2, "testCancellation").use {
        val job = GlobalScope.launch(it) {
            runBlocking(coroutineContext) {
                while (true) {
                    yield()
                }
            }
        }

        runBlocking {
            job.cancelAndJoin()
        }
    }
}

