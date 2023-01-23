/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.native.concurrent.*
import kotlin.test.*

class MultithreadedDispatchersTest {
    /**
     * Test that [newFixedThreadPoolContext] does not allocate more dispatchers than it needs to.
     * Incidentally also tests that it will allocate enough workers for its needs. Otherwise, the test will hang.
     */
    @Test
    fun testNotAllocatingExtraDispatchers() {
        suspend fun spin(set: MutableSet<Worker>) {
            repeat(100) {
                set.add(Worker.current)
                delay(1)
            }
        }
        val dispatcher = newFixedThreadPoolContext(64, "test")
        try {
            runBlocking {
                val encounteredWorkers = mutableSetOf<Worker>()
                var canStart1 = false
                var canStart2 = false
                val coroutine1 = launch(dispatcher) {
                    while (!canStart1) {
                        // intentionally empty
                    }
                    canStart2 = true
                    spin(encounteredWorkers)
                }
                val coroutine2 = launch(dispatcher) {
                    canStart1 = true
                    while (!canStart2) {
                        // intentionally empty
                    }
                    spin(encounteredWorkers)
                }
                listOf(coroutine1, coroutine2).joinAll()
                assertEquals(2, encounteredWorkers.size)
            }
        } finally {
            dispatcher.close()
        }
    }
}
