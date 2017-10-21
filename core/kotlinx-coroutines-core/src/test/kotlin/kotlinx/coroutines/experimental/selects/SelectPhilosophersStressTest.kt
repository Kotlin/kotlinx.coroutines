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

package kotlinx.coroutines.experimental.selects

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.sync.Mutex
import org.junit.Assert.assertTrue
import org.junit.Test

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
        println("--- SelectPhilosophersStressTest")
        val timeLimit = System.currentTimeMillis() + TEST_DURATION
        val philosophers = List<Deferred<Int>>(n) { id ->
            async(CommonPool) {
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