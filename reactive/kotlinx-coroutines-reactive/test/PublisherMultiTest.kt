/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*
import org.junit.Test
import kotlin.test.*

class PublisherMultiTest : TestBase() {
    @Test
    fun testConcurrentStress() = runBlocking {
        val n = 10_000 * stressTestMultiplier
        val observable = publish {
            // concurrent emitters (many coroutines)
            val jobs = List(n) {
                // launch
                launch(Dispatchers.Default) {
                    send(it)
                }
            }
            jobs.forEach { it.join() }
        }
        val resultSet = mutableSetOf<Int>()
        observable.collect {
            assertTrue(resultSet.add(it))
        }
        assertEquals(n, resultSet.size)
    }

    @Test
    fun testConcurrentStressOnSend() = runBlocking {
        val n = 10_000 * stressTestMultiplier
        val observable = publish<Int> {
            // concurrent emitters (many coroutines)
            val jobs = List(n) {
                // launch
                launch(Dispatchers.Default) {
                    select<Unit> {
                        onSend(it) {}
                    }
                }
            }
            jobs.forEach { it.join() }
        }
        val resultSet = mutableSetOf<Int>()
        observable.collect {
            assertTrue(resultSet.add(it))
        }
        assertEquals(n, resultSet.size)
    }
}
