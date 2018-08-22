/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.selects

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.sync.*
import org.junit.*
import org.junit.Assert.*
import kotlin.coroutines.experimental.*

class SelectPhilosophersStressTest : TestBase() {
    val TEST_DURATION = 3000L * stressTestMultiplier

    val n = 10 // number of philosophers
    val forks = Array<Mutex>(n) { Mutex() }

    suspend fun eat(id: Int, desc: String) {
        val left = forks[id]
        val right = forks[(id + 1) % n]
        while (true) {
            val pair = selectUnbiased<Pair<Mutex, Mutex>> {
                left.onLock(desc) { left to right }
                right.onLock(desc) { right to left }
            }
            if (pair.second.tryLock(desc)) break
            pair.first.unlock(desc)
            pair.second.lock(desc)
            if (pair.first.tryLock(desc)) break
            pair.second.unlock(desc)
        }
        assertTrue(left.isLocked && right.isLocked)
        // om, nom, nom --> eating!!!
        right.unlock(desc)
        left.unlock(desc)
    }

    @Test
    fun testPhilosophers() = runBlocking<Unit> {
        val timeLimit = System.currentTimeMillis() + TEST_DURATION
        val philosophers = List<Deferred<Int>>(n) { id ->
            async {
                val desc = "Philosopher $id"
                var eatsCount = 0
                while (System.currentTimeMillis() < timeLimit) {
                    eat(id, desc)
                    eatsCount++
                    yield()
                }
                println("Philosopher $id done, eats $eatsCount times")
                eatsCount
            }
        }
        val debugJob = launch(coroutineContext) {
            delay(3 * TEST_DURATION)
            println("Test is failing. Lock states are:")
            forks.withIndex().forEach { (id, mutex) -> println("$id: $mutex") }
        }
        val eats = withTimeout(5 * TEST_DURATION) { philosophers.map { it.await() } }
        debugJob.cancel()
        eats.withIndex().forEach { (id, eats) ->
            assertTrue("$id shall not starve", eats > 0)
        }
    }
}