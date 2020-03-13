/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.jdk9

import kotlinx.coroutines.*
import org.junit.Test
import kotlin.test.*

class PublisherMultiTest : TestBase() {
    @Test
    fun testConcurrentStress() = runBlocking {
        val n = 10_000 * stressTestMultiplier
        val observable = flowPublish {
            // concurrent emitters (many coroutines)
            val jobs = List(n) {
                // launch
                launch {
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
}
