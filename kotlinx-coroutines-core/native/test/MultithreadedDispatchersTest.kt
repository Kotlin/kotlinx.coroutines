/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.internal.*
import kotlin.native.concurrent.*
import kotlin.test.*

private class BlockingBarrier(val n: Int) {
    val counter = atomic(0)
    val wakeUp = Channel<Unit>(n - 1)
    fun await() {
        val count = counter.addAndGet(1)
        if (count == n) {
            repeat(n - 1) {
                runBlocking {
                    wakeUp.send(Unit)
                }
            }
        } else if (count < n) {
            runBlocking {
                wakeUp.receive()
            }
        }
    }
}

class MultithreadedDispatchersTest {
    /**
     * Test that [newFixedThreadPoolContext] does not allocate more dispatchers than it needs to.
     * Incidentally also tests that it will allocate enough workers for its needs. Otherwise, the test will hang.
     */
    @Test
    fun testNotAllocatingExtraDispatchers() {
        val barrier = BlockingBarrier(2)
        val lock = SynchronizedObject()
        suspend fun spin(set: MutableSet<Worker>) {
            repeat(100) {
                synchronized(lock) { set.add(Worker.current) }
                delay(1)
            }
        }
        val dispatcher = newFixedThreadPoolContext(64, "test")
        try {
            runBlocking {
                val encounteredWorkers = mutableSetOf<Worker>()
                val coroutine1 = launch(dispatcher) {
                    barrier.await()
                    spin(encounteredWorkers)
                }
                val coroutine2 = launch(dispatcher) {
                    barrier.await()
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
