/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.reactive

import kotlinx.coroutines.experimental.*
import org.hamcrest.core.*
import org.junit.*
import org.junit.Assert.*

class PublisherMultiTest : TestBase() {
    @Test
    fun testConcurrentStress() = runBlocking {
        val n = 10_000 * stressTestMultiplier
        val observable = GlobalScope.publish {
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
        observable.consumeEach {
            assertTrue(resultSet.add(it))
        }
        assertThat(resultSet.size, IsEqual(n))
    }
}
